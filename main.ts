// Tiny stack VM: answers i001..i040 of one set per ISA.md, traps included.
// Reads <id>/program.bin + <id>/input.bin, writes <id>/stdout.bin + exit.txt.
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
const I = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const O = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
function R(p, q) {
  const n = p.length, S = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256), o = new Uint8Array(65536);
  let s = 0, c = 0, l = 0, j = 0, x = 0, t = 0;
  const E = (v) => [o.slice(0, l), v];
  for (;;) {
    if (t === 1e6) return E(10);
    if (x < 0 || x >= n) return E(9);
    const b = p[x];
    t++;
    switch (b) {
      case 0: return E(0); // HALT
      case 1: // PUSH8, sign-extended
        if (x + 1 >= n) return E(9);
        if (s > 255) return E(3);
        S[s++] = (p[x + 1] << 24) >> 24; x += 2; break;
      case 2: // PUSH32, little-endian
        if (x + 4 >= n) return E(9);
        if (s > 255) return E(3);
        S[s++] = p[x + 1] | (p[x + 2] << 8) | (p[x + 3] << 16) | (p[x + 4] << 24); x += 5; break;
      case 3: // POP
        if (s < 1) return E(2);
        s--; x++; break;
      case 4: // DUP
        if (s < 1) return E(2);
        if (s > 255) return E(3);
        S[s] = S[s - 1]; s++; x++; break;
      case 5: // SWAP
        if (s < 2) return E(2);
        { const v = S[s - 1]; S[s - 1] = S[s - 2]; S[s - 2] = v; }
        x++; break;
      case 6: // OVER
        if (s < 2) return E(2);
        if (s > 255) return E(3);
        S[s] = S[s - 2]; s++; x++; break;
      case 7: // ROT: (a b c -- b c a)
        if (s < 3) return E(2);
        { const v = S[s - 3]; S[s - 3] = S[s - 2]; S[s - 2] = S[s - 1]; S[s - 1] = v; }
        x++; break;
      case 23: // NEG, wraps
        if (s < 1) return E(2);
        S[s - 1] = (-S[s - 1]) | 0; x++; break;
      case 27: // NOT
        if (s < 1) return E(2);
        S[s - 1] = ~S[s - 1]; x++; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: { // two-operand ops: (a b -- r)
        if (s < 2) return E(2);
        const y = S[s - 1], a = S[s - 2];
        let r = 0;
        if (b === 16) r = (a + y) | 0;
        else if (b === 17) r = (a - y) | 0;
        else if (b === 18) r = Math.imul(a, y);
        else if (b === 19) { if (!y) return E(4); r = a === -2147483648 && y === -1 ? a : (a / y) | 0; }
        else if (b === 20) { if (!y) return E(4); r = y === -1 ? 0 : (a % y) | 0; }
        else if (b === 21) { if (!y) return E(4); r = Math.floor((a >>> 0) / (y >>> 0)) | 0; }
        else if (b === 22) { if (!y) return E(4); r = ((a >>> 0) % (y >>> 0)) | 0; }
        else if (b === 24) r = a & y;
        else if (b === 25) r = a | y;
        else if (b === 26) r = a ^ y;
        else if (b === 28) r = a << (y & 31);
        else if (b === 29) r = a >> (y & 31);
        else if (b === 30) r = (a >>> (y & 31)) | 0;
        else if (b === 32) r = a === y ? 1 : 0;
        else if (b === 33) r = a < y ? 1 : 0;
        else r = (a >>> 0) < (y >>> 0) ? 1 : 0;
        S[s - 2] = r; s--; x++; break;
      }
      case 48: // JMP: signed 16-bit offset from next instruction
        if (x + 2 >= n) return E(9);
        x = x + 3 + (((p[x + 1] | (p[x + 2] << 8)) << 16) >> 16); break;
      case 49: case 50: { // JZ / JNZ
        if (x + 2 >= n) return E(9);
        if (s < 1) return E(2);
        const v = S[--s], rel = ((p[x + 1] | (p[x + 2] << 8)) << 16) >> 16;
        x = x + 3;
        if ((b === 49) === (v === 0)) x += rel;
        break;
      }
      case 51: // CALL: unsigned 16-bit absolute target
        if (x + 2 >= n) return E(9);
        if (c >= 64) return E(7);
        C[c++] = x + 3; x = p[x + 1] | (p[x + 2] << 8); break;
      case 52: // RET
        if (c === 0) return E(8);
        x = C[--c]; break;
      case 64: // LOAD
        if (s < 1) return E(2);
        { const a = S[s - 1]; if (a < 0 || a > 255) return E(6); S[s - 1] = M[a]; }
        x++; break;
      case 65: // STORE: (v addr --)
        if (s < 2) return E(2);
        { const a = S[s - 1]; if (a < 0 || a > 255) return E(6); M[a] = S[s - 2]; s -= 2; }
        x++; break;
      case 80: { // PRINT: decimal ASCII; over the limit traps 11, writes nothing
        if (s < 1) return E(2);
        const d = String(S[s - 1]);
        if (l + d.length > 65536) return E(11);
        for (let i = 0; i < d.length; i++) o[l++] = d.charCodeAt(i);
        s--; x++; break;
      }
      case 81: // PUTC
        if (s < 1) return E(2);
        if (l >= 65536) return E(11);
        o[l++] = S[--s] & 255; x++; break;
      case 82: // IN: next input byte, -1 once input is used up
        if (s > 255) return E(3);
        S[s++] = j < q.length ? q[j++] : -1; x++; break;
      case 83: // EXIT: low byte of the popped value
        if (s < 1) return E(2);
        return E(S[--s] & 255);
      default: return E(5); // unknown opcode
    }
  }
}
for (let k = 1; k <= 40; k++) {
  const id = "i" + String(k).padStart(3, "0");
  let p = new Uint8Array(0), q = new Uint8Array(0);
  try { p = new Uint8Array(readFileSync(join(I, id, "program.bin"))); } catch {}
  try { q = new Uint8Array(readFileSync(join(I, id, "input.bin"))); } catch {}
  const [o, v] = R(p, q);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, "stdout.bin"), o);
  writeFileSync(join(O, id, "exit.txt"), v + "\n");
}
