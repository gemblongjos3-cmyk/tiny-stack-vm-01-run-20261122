// Tiny stack VM, make.fun tiny-stack-vm-01 ISA v1. One run answers a whole
// set: for each /input/<id>/ it runs program.bin on input.bin and writes
// /output/<id>/stdout.bin + exit.txt. Pure and deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
// [byte, immediate bytes, pops, pushes] for the 37 opcodes; anything else is trap 5.
const OPS = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
];
const IMM = new Uint8Array(256), POPN = new Uint8Array(256), PSHN = new Uint8Array(256), KNOWN = new Uint8Array(256);
for (const [b, im, po, pu] of OPS) { IMM[b] = im; POPN[b] = po; PSHN[b] = pu; KNOWN[b] = 1; }

// Run one program. Returns [stdout bytes, exit code]. Traps: 2 underflow,
// 3 overflow, 4 div by zero, 5 unknown opcode, 6 bad memory address,
// 7 call depth, 8 empty RET, 9 pc outside / truncated immediate,
// 10 step limit, 11 output limit.
function run(prog, inp) {
  const n = prog.length;
  const S = new Int32Array(256); let sp = 0; // data stack
  const C = new Int32Array(64); let cp = 0; // call stack
  const M = new Int32Array(256); // memory, 256 words
  const out = new Uint8Array(65536); let ol = 0;
  let ip = 0, pc = 0, steps = 0;
  const end = (code) => [out.subarray(0, ol), code];
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    if (!KNOWN[op]) return end(5);
    const im = IMM[op];
    if (pc + im >= n) return end(9);
    steps++;
    const nx = pc + 1 + im;
    const po = POPN[op];
    if (sp < po) return end(2);
    if (sp - po + PSHN[op] > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: S[sp++] = (prog[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: S[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break; // PUSH32 LE
      case 0x03: sp--; break;
      case 0x04: S[sp] = S[sp - 1]; sp++; break;
      case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; }
      case 0x06: S[sp] = S[sp - 2]; sp++; break;
      case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; }
      case 0x17: S[sp - 1] = (-S[sp - 1]) | 0; break; // NEG wraps at INT_MIN
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1], a = S[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // low 32 bits
        else if (op === 0x13) { if (b === 0) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; } // DIV truncates toward 0
        else if (op === 0x14) { if (b === 0) return end(4); r = b === -1 ? 0 : (a % b) | 0; } // MOD, sign of a
        else if (op === 0x15) { if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
        else if (op === 0x16) { if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31); // arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // logical
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp -= 2; S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset from next
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = S[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel; // target unchecked: out-of-range traps next step
        break;
      }
      case 0x33: // CALL, unsigned 16-bit target
        if (cp === 64) return end(7);
        C[cp++] = nx; pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34: if (cp === 0) return end(8); pc = C[--cp]; break; // RET
      case 0x40: { const a = S[sp - 1]; if (a < 0 || a >= 256) return end(6); S[sp - 1] = M[a]; break; }
      case 0x41: { const a = S[sp - 1], v = S[sp - 2]; if (a < 0 || a >= 256) return end(6); sp -= 2; M[a] = v; break; }
      case 0x50: { // PRINT decimal ASCII, no newline; over-limit writes nothing
        const s = String(S[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51: if (ol + 1 > 65536) return end(11); out[ol++] = S[--sp] & 255; break; // PUTC
      case 0x52: S[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN, -1 past end
      case 0x53: return end(S[--sp] & 255); // EXIT, low byte
    }
  }
}
for (const id of readdirSync(IN_DIR).sort()) {
  let prog, inp = new Uint8Array(0);
  try { prog = readFileSync(join(IN_DIR, id, 'program.bin')); } catch { continue; }
  try { inp = readFileSync(join(IN_DIR, id, 'input.bin')); } catch { /* empty input */ }
  let stdout, exit;
  try { [stdout, exit] = run(prog, inp); }
  catch { stdout = new Uint8Array(0); exit = 9; } // never let one bad instance kill the set
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), stdout);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), exit + '\n');
}
