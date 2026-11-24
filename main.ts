// Tiny stack VM for make.fun tiny-stack-vm-01: runs every bytecode program in
// /input/<id>/ (program.bin + input.bin) and writes /output/<id>/stdout.bin
// and /output/<id>/exit.txt. Implements the ISA in generator/subject/ISA.md:
// 32-bit wrapping integers, 256-value data stack, 64-deep call stack,
// 256 words of memory, traps 2-11 with their exit codes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Run one program; returns [exitCode, outputBytes].
function runVM(prog, inp) {
  const mem = new Int32Array(256);
  const st = new Int32Array(257);
  const cs = new Int32Array(64);
  const out = [];
  let sp = 0, csp = 0, pc = 0, steps = 0, ip = 0;
  for (;;) {
    if (steps >= 1000000) return [10, out];
    if (pc < 0 || pc >= prog.length) return [9, out];
    const op = prog[pc];
    // Immediate lengths: PUSH8 1, PUSH32 4, JMP/JZ/JNZ/CALL 2, others 0.
    let imm = 0;
    if (op === 1) imm = 1;
    else if (op === 2) imm = 4;
    else if (op === 48 || op === 49 || op === 50 || op === 51) imm = 2;
    else if (
      op !== 0 && op !== 3 && op !== 4 && op !== 5 && op !== 6 && op !== 7 &&
      op !== 16 && op !== 17 && op !== 18 && op !== 19 && op !== 20 && op !== 21 &&
      op !== 22 && op !== 23 && op !== 24 && op !== 25 && op !== 26 && op !== 27 &&
      op !== 28 && op !== 29 && op !== 30 && op !== 32 && op !== 33 && op !== 34 &&
      op !== 52 && op !== 53 && op !== 64 && op !== 65 && op !== 80 && op !== 81 &&
      op !== 82 && op !== 83
    ) return [5, out];
    if (pc + 1 + imm > prog.length) return [9, out];
    steps++;
    // Helpers below read operands after the underflow/overflow checks.
    if (op === 0) return [0, out];
    if (op === 1) {
      if (sp >= 256) return [3, out];
      let v = prog[pc + 1];
      if (v >= 128) v -= 256;
      st[sp++] = v; pc += 2;
    } else if (op === 2) {
      if (sp >= 256) return [3, out];
      st[sp++] = (prog[pc + 1] | (prog[pc + 2] << 8) | (prog[pc + 3] << 16) | (prog[pc + 4] << 24));
      pc += 5;
    } else if (op === 3) {
      if (sp < 1) return [2, out];
      sp--; pc++;
    } else if (op === 4) {
      if (sp < 1) return [2, out];
      if (sp >= 256) return [3, out];
      st[sp] = st[sp - 1]; sp++; pc++;
    } else if (op === 5) {
      if (sp < 2) return [2, out];
      const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; pc++;
    } else if (op === 6) {
      if (sp < 2) return [2, out];
      if (sp >= 256) return [3, out];
      st[sp] = st[sp - 2]; sp++; pc++;
    } else if (op === 7) {
      if (sp < 3) return [2, out];
      const a = st[sp - 3], b = st[sp - 2], c = st[sp - 1];
      st[sp - 3] = b; st[sp - 2] = c; st[sp - 1] = a; pc++;
    } else if (op >= 16 && op <= 34) {
      if (op === 23 || op === 27) {
        if (sp < 1) return [2, out];
        const a = st[sp - 1];
        st[sp - 1] = op === 23 ? (-a) | 0 : ~a;
        pc++;
      } else {
        if (sp < 2) return [2, out];
        const b = st[--sp], a = st[--sp];
        let r = 0;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19 || op === 20) {
          if (b === 0) return [4, out];
          r = op === 19 ? (Math.trunc(a / b)) | 0 : (a % b) | 0;
        } else if (op === 21 || op === 22) {
          if (b === 0) return [4, out];
          const ua = a >>> 0, ub = b >>> 0;
          r = op === 21 ? (Math.trunc(ua / ub)) | 0 : (ua % ub) | 0;
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        st[sp++] = r; pc++;
      }
    } else if (op === 48 || op === 49 || op === 50) {
      let off = prog[pc + 1] | (prog[pc + 2] << 8);
      if (off >= 32768) off -= 65536;
      if (op === 48) { pc = pc + 3 + off; continue; }
      if (sp < 1) return [2, out];
      const v = st[--sp];
      if ((op === 49 && v === 0) || (op === 50 && v !== 0)) pc = pc + 3 + off;
      else pc += 3;
    } else if (op === 51) {
      const target = prog[pc + 1] | (prog[pc + 2] << 8);
      if (csp >= 64) return [7, out];
      cs[csp++] = pc + 3; pc = target;
    } else if (op === 52) {
      if (csp === 0) return [8, out];
      pc = cs[--csp];
    } else if (op === 64) {
      if (sp < 1) return [2, out];
      const addr = st[sp - 1];
      if (addr < 0 || addr > 255) return [6, out];
      st[sp - 1] = mem[addr]; pc++;
    } else if (op === 65) {
      if (sp < 2) return [2, out];
      const addr = st[--sp], v = st[--sp];
      if (addr < 0 || addr > 255) return [6, out];
      mem[addr] = v; pc++;
    } else if (op === 80) {
      if (sp < 1) return [2, out];
      const v = st[--sp], s = String(v);
      if (out.length + s.length > 65536) return [11, out];
      for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
      pc++;
    } else if (op === 81) {
      if (sp < 1) return [2, out];
      if (out.length + 1 > 65536) return [11, out];
      out.push(st[--sp] & 255); pc++;
    } else if (op === 82) {
      if (sp >= 256) return [3, out];
      st[sp++] = ip < inp.length ? inp[ip++] : -1;
      pc++;
    } else if (op === 83) {
      if (sp < 1) return [2, out];
      return [st[--sp] & 255, out];
    }
  }
}

for (const id of readdirSync(I).sort()) {
  // Skip anything that is not an instance directory (no program.bin).
  let prog;
  try { prog = new Uint8Array(readFileSync(join(I, id, 'program.bin'))); } catch { continue; }
  let inp = new Uint8Array(0);
  try { inp = new Uint8Array(readFileSync(join(I, id, 'input.bin'))); } catch { /* no input */ }
  const [exit, out] = runVM(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), Buffer.from(out));
  writeFileSync(join(O, id, 'exit.txt'), String(exit) + '\n');
}
