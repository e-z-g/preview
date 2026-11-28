/* nova-fieldfacts.js -- what the program does with a field, worked out
   from its code rather than typed.
   =========================================================================

   A field note (nova-fields.js) is English a session wrote after reading
   the code. These are the facts under it, found in the open release's
   program each time it is read, so they cannot go stale or be mistyped:
   every routine that reads or writes the field where it is kept
   (novaFieldHit, the places nova-fieldsites.js finds), and at each read
   the flag bits the value is tested for and the numbers it is compared
   with in the instructions after it.

   A read's value is followed through the few instructions after the load
   (NOVA_FACT_WINDOW, counted while the value is in a scratch register), through moves, sign extensions and conditional
   branches, until its register is written again, a call that may change
   it or a jump:
       lhz   r0, 2536(r2)     shïp Flags
       andi. r2, r0, 1024     tests 0x0400
       cmpwi cr7, r0, 3       compared with 3
   A bit pulled out by a rotate and mask (rlwinm, clrlwi) is the mask turned
   back by the rotation. What the bits and numbers mean is left to the note.

   GENERIC TO EV NOVA, NO DOM. LOAD ORDER: after nova-fieldsites.js. */

const NOVA_FACT_WINDOW = 80;

// Every access to an array or record place in the program, by its place
// ('g@off'): [{ routine, addr, i, load, rt }]. Cached on the program.
function novaAccessIndex(prog) {
  if (prog.accessIndex) return prog.accessIndex;
  const out = new Map();
  prog.accessIndex = out;
  for (const r of prog.routines) {
    if (r.glue) continue;
    const ops = prog.ops(r), at = new Map(ops.map((o, i) => [o.addr, i]));
    for (const { addr, a } of novaRoutineAccesses(prog, r)) {
      if (a.call || a.fp && !a.load) continue;
      const k = a.g + '@' + a.off;
      if (!out.has(k)) out.set(k, []);
      out.get(k).push({ routine: r, addr, i: at.get(addr), load: a.load, rt: a.rt, fp: a.fp, size: a.size });
    }
  }
  return out;
}

// The bits of the value before the rotation that a 32-bit rotate and mask
// lets through.
function novaRlwinmBits(sh, mb, me) {
  let mask = 0;
  for (let b = mb; ; b = (b + 1) % 32) { mask |= 1 << (31 - b); if (b === me) break; }
  mask >>>= 0;
  return ((mask >>> sh) | (mask << (32 - sh))) >>> 0;
}

/* What follows one read: { bits: [{ mask, addr }], compares: [{ value, addr }] }.
   Both ways out of a conditional branch are followed, each within the
   window, so a run of tests that branch past each other is read whole. */
function novaFactsAfter(prog, ops, i, rt) {
  const bits = [], compares = [], shifts = [], seen = new Set(), byAddr = new Map(ops.map((o, k) => [o.addr, k]));
  const work = [{ k: i + 1, regs: new Set([rt]), left: NOVA_FACT_WINDOW }];
  while (work.length) {
    let { k, regs, left } = work.pop();
    const made = new Set();   // registers holding a mask made by a shift
    // the window counts down only while the value is in a scratch register, since a saved one (r13 to r31) has it until something writes it
    for (; k < ops.length && left > 0; k++, left -= [...regs].some(r => r < 13) ? 1 : 0) {
      if (seen.has(k)) break;
      seen.add(k);
      const o = ops[k], op = o.op;
      if (!op) break;
      if (op.branch) {
        // a call may change r0 and r3 to r12 (r2 too in the Mach-O), and leaves the rest
        if (op.lk && o.target != null && novaLeavesRegisters(prog, o.target)) continue;
        if (op.lk) { for (const r of [0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].concat(prog.kind === 'macho' ? [2] : [])) { regs.delete(r); made.delete(r); } if (!regs.size) break; continue; }
        const to = op.disp !== undefined && !op.aa ? byAddr.get(o.addr + op.disp) : undefined;
        if (to !== undefined && to > k) work.push({ k: to, regs: new Set(regs), left: left - 1 });
        if (!op.conditional || (op.bo & 0x14) === 0x14) break;
        continue;
      }
      if (op.mn === 'andi.' && regs.has(op.rs)) bits.push({ mask: op.imm & 0xffff, addr: o.addr });
      else if (op.mn === 'andis.' && regs.has(op.rs)) bits.push({ mask: ((op.imm & 0xffff) << 16) >>> 0, addr: o.addr });
      else if (/^(rlwinm|clrlwi|slwi|srwi|extrwi|rotlwi)\.?$/.test(op.mn) && regs.has(op.rs) && op.mb !== undefined) {
        const mask = novaRlwinmBits(op.sh || 0, op.mb, op.me);
        // a zero extension of a half word or a byte is the whole value, not a bit,
        // and a mask of more than eight bits passes the value on (clearing the top bit), not a test
        const n = mask.toString(2).replace(/0/g, '').length;
        if (mask === 0xffff || mask === 0xff || n > 8) regs.add(op.ra);
        else bits.push({ mask, addr: o.addr });
      }
      else if ((op.mn === 'cmpwi' || op.mn === 'cmplwi') && regs.has(op.ra)) {
        // a signed compare with 0 that a branch reads as less or greater tests the sign, the top bit
        const br = ops.slice(k + 1, k + 9).find(q => q.op && q.op.branch && q.op.conditional && q.op.bi >> 2 === (op.crf || 0));
        compares.push({ value: op.imm, addr: o.addr, sign: op.mn === 'cmpwi' && op.imm === 0 && !!br && (br.op.bi & 3) < 2 });
      }
      else if (/^(extsh|extsb|mr)\.?$/.test(op.mn) && regs.has(op.rs)) regs.add(op.ra);
      // shifted by a register (sraw r0, r0, r9, then andi. 1): any bit, by number
      else if (/^(sraw|srw|slw)\.?$/.test(op.mn) && regs.has(op.rs)) shifts.push({ addr: o.addr });
      // or a mask made by a shift (li r4, 1; slw r0, r4, r3; and. r0, r5, r0)
      else if (/^and\.?$/.test(op.mn) && (regs.has(op.rs) && made.has(op.rb) || regs.has(op.rb) && made.has(op.rs))) shifts.push({ addr: o.addr });
      if (/^(slw|srw|sraw)\.?$/.test(op.mn) && !regs.has(op.rs)) made.add(op.ra); else if (op.rd !== undefined) made.delete(op.rd); else if (op.ra !== undefined && op.rs !== undefined && op.d === undefined) made.delete(op.ra);
      // the value's register written by anything else
      // a float instruction's registers are float registers (lfd f30 leaves r30 alone)
      const w = /^(l|st)?f/.test(op.mn) ? undefined : op.rd !== undefined ? op.rd : op.rs !== undefined && op.ra !== undefined && op.d === undefined ? op.ra : op.mn[0] === 'l' ? op.rt : undefined;
      // (a move, extension or mask of the value itself still has the value, as above, and one of another register replaces it)
      const copied = /^(extsh|extsb|mr|clrlwi|rlwinm)\.?$/.test(op.mn) && regs.has(op.rs);
      if (w !== undefined && regs.has(w) && !copied) regs.delete(w);
      if (!regs.size) break;
    }
  }
  return { bits, compares, shifts };
}

/* A field's facts in the open program: { reads: [{ routine, addr }],
   writes: [{ routine, addr }], bits: Map mask -> [addr], compares: Map
   value -> [addr], signs: [addr] (the compares with 0 that test the
   sign), shifts: [addr] (where a bit is picked by number, which tests
   them all) }, or null for a field with no place found. A byte read
   of a two-byte field's half is a read of the field (lbz r0, 33(r2) for
   the flags at 32, then clrlwi r0, r0, 31 tests 0x0001), the high byte's
   bits moved up eight. */
function novaFieldFacts(prog, type, field) {
  const kept = novaFieldHit(prog, type, field);
  if (!kept) return null;
  const layout = (novaLayout(type) || []).find(f => f.name === field), two = layout && layout.size === 2;
  const index = novaAccessIndex(prog), places = [];
  for (const g of kept.direct) for (const off of kept.recs) places.push([g, off]);
  for (const t of kept.arrays) for (const off of t.offs) places.push([t.g, off]);
  // [key, shift, only byte accesses]
  const keys = new Map();
  for (const [g, off] of places) { keys.set(g + '@' + off, false); if (two) keys.set(g + '@' + (off + 1), true); }
  const reads = [], writes = [], bits = new Map(), compares = new Map(), signs = [], shifts = [];
  const add = (m, k, addr) => { if (!m.has(k)) m.set(k, []); m.get(k).push(addr); };
  for (const [k, low] of keys) for (const x of index.get(k) || []) {
    if (low && x.size !== 1) continue;
    const shift = two && !low && x.size === 1 ? 8 : 0;
    if (!x.load) { writes.push({ routine: x.routine, addr: x.addr }); continue; }
    reads.push({ routine: x.routine, addr: x.addr });
    if (x.fp || x.i === undefined) continue;
    const f = novaFactsAfter(prog, prog.ops(x.routine), x.i, x.rt);
    for (const b of f.bits) add(bits, (b.mask << shift) & 0xffffffff, b.addr);
    for (const c of f.compares) { add(compares, c.value, c.addr); if (c.sign) signs.push(c.addr); }
    for (const x of f.shifts) shifts.push(x.addr);
  }
  const order = (x, y) => x.addr - y.addr;
  return { reads: reads.sort(order), writes: writes.sort(order), bits, compares, signs, shifts };
}
