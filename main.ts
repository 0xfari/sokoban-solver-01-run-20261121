// Sokoban solver: split the level into independent rooms off one hallway;
// solve each room push-optimally with A* over pushes (player region
// normalised away); stitch rooms with hallway walks. Deterministic:
// budgets count expansions, never the clock.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DX = [0, 0, -1, 1], DY = [-1, 1, 0, 0], CH = ['u', 'd', 'l', 'r'];
const RB = 150000, EB = 300000, GB = 300000;
function nb(w, h, c, k) {
  const x = c % w, y = (c / w) | 0;
  if (k === 0) return y > 0 ? c - w : -1;
  if (k === 1) return y < h - 1 ? c + w : -1;
  if (k === 2) return x > 0 ? c - 1 : -1;
  return x < w - 1 ? c + 1 : -1;
}
function parse(t) {
  const rows = t.split('\n').map((r) => r.replace(/\r$/, '')).filter((r) => r.length > 0);
  const w = Math.max(...rows.map((r) => r.length)), h = rows.length;
  const wall = new Array(w * h).fill(true), goals = [];
  let boxes = [], player = 0;
  rows.forEach((row, y) => {
    for (let x = 0; x < w; x++) {
      const c = row[x] ?? '#', i = y * w + x;
      wall[i] = c === '#';
      if (c === '.' || c === '*' || c === '+') goals.push(i);
      if (c === '$' || c === '*') boxes.push(i);
      if (c === '@' || c === '+') player = i;
    }
  });
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}
function split(g) {
  const { w, h, wall, player } = g, hy = (player / w) | 0, hall = new Set();
  for (let x = 0; x < w; x++) { const i = hy * w + x; if (!wall[i]) hall.add(i); }
  const seen = new Set(), rooms = [];
  for (let i = 0; i < w * h; i++) {
    if (wall[i] || ((i / w) | 0) === hy || seen.has(i)) continue;
    const cells = [], q = [i];
    seen.add(i);
    for (let qi = 0; qi < q.length; qi++) {
      const c = q[qi];
      cells.push(c);
      for (let k = 0; k < 4; k++) {
        const n = nb(w, h, c, k);
        if (n < 0 || wall[n] || ((n / w) | 0) === hy || seen.has(n)) continue;
        seen.add(n); q.push(n);
      }
    }
    const cs = new Set(cells);
    const boxes = g.boxes.filter((b) => cs.has(b)), goals = g.goals.filter((x) => cs.has(x));
    if (!boxes.length) continue;
    const entries = [];
    for (const c of cells) for (let k = 0; k < 4; k++) {
      const n = nb(w, h, c, k);
      if (n >= 0 && hall.has(n) && !entries.includes(n)) entries.push(n);
    }
    if (!entries.length) return null;
    rooms.push({ cells: cs, boxes, goals, entries });
  }
  if (rooms.reduce((a, r) => a + r.boxes.length, 0) !== g.boxes.length) return null;
  return { rooms, hy, hall };
}
function ctx(g, floor, goals) {
  const { w, h } = g, F = floor instanceof Set ? floor : new Set(floor), goalSet = new Set(goals), dist = new Map();
  for (const c of F) {
    const d = new Int16Array(w * h).fill(-1);
    d[c] = 0;
    const q = [c];
    for (let qi = 0; qi < q.length; qi++) {
      const cur = q[qi];
      for (let k = 0; k < 4; k++) {
        const n = nb(w, h, cur, k);
        if (n < 0 || !F.has(n) || d[n] >= 0) continue;
        d[n] = d[cur] + 1; q.push(n);
      }
    }
    dist.set(c, d);
  }
  const dead = new Set();
  for (const c of F) {
    if (goalSet.has(c)) continue;
    const up = !F.has(nb(w, h, c, 0)), dn = !F.has(nb(w, h, c, 1));
    const lf = !F.has(nb(w, h, c, 2)), rt = !F.has(nb(w, h, c, 3));
    if ((up || dn) && (lf || rt)) { dead.add(c); continue; }
    for (let k = 0; k < 4; k++) {
      if (F.has(nb(w, h, c, k))) continue;
      const step = k < 2 ? 1 : w, row = (c / w) | 0;
      let ok = false, closed = 0;
      for (const s of [1, -1]) {
        let open = false;
        for (let t = 0; ; t++) {
          const cc = c + s * t * step;
          if (step === 1 && ((cc / w) | 0) !== row) break;
          if (!F.has(cc)) break;
          if (F.has(nb(w, h, cc, k))) { open = true; break; }
          if (goalSet.has(cc)) { ok = true; break; }
        }
        if (ok) break;
        if (!open) closed++;
      }
      if (!ok && closed === 2) { dead.add(c); break; }
    }
  }
  return { w, h, F, goals, goalSet, dist, dead };
}
function perms(n) {
  const out = [], a = [...Array(n).keys()];
  const gen = (i) => {
    if (i === n) { out.push(a.slice()); return; }
    for (let j = i; j < n; j++) { [a[i], a[j]] = [a[j], a[i]]; gen(i + 1); [a[i], a[j]] = [a[j], a[i]]; }
  };
  gen(0);
  return out;
}
function heur(c) {
  const { goals, dist } = c, n = goals.length, ps = n <= 5 ? perms(n) : null;
  return (bs) => {
    if (ps) {
      let best = Infinity;
      for (const p of ps) {
        let s = 0;
        for (let i = 0; i < n; i++) {
          const d = dist.get(bs[i])[goals[p[i]]];
          if (d < 0) { s = Infinity; break; }
          s += d;
        }
        if (s < best) best = s;
      }
      return best;
    }
    let s = 0;
    for (const b of bs) {
      let m = Infinity;
      for (const gl of goals) { const d = dist.get(b)[gl]; if (d >= 0 && d < m) m = d; }
      if (m === Infinity) return Infinity;
      s += m;
    }
    return s;
  };
}
function region(c, start, boxSet) {
  const { w, h, F } = c, seen = new Set([start]), q = [start];
  let rep = start;
  for (let qi = 0; qi < q.length; qi++) {
    const cur = q[qi];
    if (cur < rep) rep = cur;
    for (let k = 0; k < 4; k++) {
      const n = nb(w, h, cur, k);
      if (n < 0 || !F.has(n) || boxSet.has(n) || seen.has(n)) continue;
      seen.add(n); q.push(n);
    }
  }
  return { rep, set: seen };
}
function walk(c, start, target, boxSet) {
  if (start === target) return '';
  const { w, h, F } = c, prev = new Map([[start, -1]]), step = new Map(), q = [start];
  for (let qi = 0; qi < q.length; qi++) {
    const cur = q[qi];
    for (let k = 0; k < 4; k++) {
      const n = nb(w, h, cur, k);
      if (n < 0 || !F.has(n) || boxSet.has(n) || prev.has(n)) continue;
      prev.set(n, cur); step.set(n, k);
      if (n === target) {
        let s = '';
        for (let t = n; t !== start; t = prev.get(t)) s = CH[step.get(t)] + s;
        return s;
      }
      q.push(n);
    }
  }
  return null;
}
function dead(c, boxes) {
  const { w, h, F, goalSet } = c, boxSet = new Set(boxes);
  for (const b of boxes) if (!goalSet.has(b) && c.dead.has(b)) return true;
  for (const b of boxes) {
    if (goalSet.has(b)) continue;
    const x = b % w, y = (b / w) | 0;
    for (const [ox, oy] of [[-1, -1], [0, -1], [-1, 0], [0, 0]]) {
      let blocked = true, hasBox = false, hasGoal = false;
      for (let dy = 0; dy < 2; dy++) for (let dx = 0; dx < 2; dx++) {
        const cx = x + ox + dx, cy = y + oy + dy;
        if (cx < 0 || cx >= w || cy < 0 || cy >= h) continue;
        const cell = cy * w + cx;
        if (goalSet.has(cell)) hasGoal = true;
        if (boxSet.has(cell)) hasBox = true;
        else if (F.has(cell)) blocked = false;
      }
      if (blocked && hasBox && !hasGoal) return true;
    }
  }
  const frozen = new Set();
  let changed = true;
  while (changed) {
    changed = false;
    for (const b of boxes) {
      if (goalSet.has(b) || frozen.has(b)) continue;
      const blk = (cell) => !F.has(cell) || (boxSet.has(cell) && frozen.has(cell));
      if (blk(nb(w, h, b, 2)) && blk(nb(w, h, b, 3)) && blk(nb(w, h, b, 0)) && blk(nb(w, h, b, 1))) {
        frozen.add(b); changed = true;
      }
    }
  }
  return frozen.size > 0;
}
function replay(c, startPlayer, boxes0, pushes) {
  const { w } = c;
  let player = startPlayer;
  const cur = boxes0.slice();
  let moves = '';
  for (const pu of pushes) {
    const d = DY[pu.dir] * w + DX[pu.dir], path = walk(c, player, pu.from - d, new Set(cur));
    if (path === null) return null;
    moves += path + CH[pu.dir];
    const bi = cur.indexOf(pu.from);
    cur[bi] = pu.from + d; cur.sort((a, b) => a - b);
    player = pu.from;
  }
  return { moves, pushes: pushes.length, finalPlayer: player, finalBoxes: cur };
}
const keyOf = (rep, bs) => String.fromCharCode(rep, ...bs);
function astar(c, startPlayer, boxes0, exitCells, exitReq, budget) {
  const { w, F, goalSet } = c, n = boxes0.length, h = heur(c);
  const sp = [], sb = [], sg = [], parent = [], pfrom = [], pdir = [], best = new Map(), heap = [];
  const less = (a, b) => a[0] < b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] < b[2])));
  const push = (e) => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i], heap[p])) break;
      [heap[i], heap[p]] = [heap[p], heap[i]]; i = p;
    }
  };
  const pop = () => {
    const top = heap[0], last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let ch = 2 * i + 1;
        if (ch >= heap.length) break;
        if (ch + 1 < heap.length && less(heap[ch + 1], heap[ch])) ch++;
        if (!less(heap[ch], heap[i])) break;
        [heap[i], heap[ch]] = [heap[ch], heap[i]]; i = ch;
      }
    }
    return top;
  };
  const add = (rep, bs, g, par, from, dir) => {
    const t = sp.length;
    sp.push(rep); sb.push(bs); sg.push(g); parent.push(par); pfrom.push(from); pdir.push(dir);
    best.set(keyOf(rep, bs), t);
    return t;
  };
  const b0 = boxes0.slice().sort((a, b) => a - b);
  const rep0 = region(c, startPlayer, new Set(b0)).rep, h0 = h(b0);
  if (!isFinite(h0) || dead(c, b0)) return null;
  let seq = 0;
  const root = add(rep0, b0, 0, -1, -1, -1);
  push([h0, 0, seq++, root]);
  let expanded = 0;
  while (heap.length > 0 && expanded < budget) {
    const [, g, s] = pop();
    if (best.get(keyOf(sp[s], sb[s])) !== s) continue;
    const bs = sb[s];
    if (bs.every((b) => goalSet.has(b))) {
      if (!exitReq || exitCells.some((e) => region(c, sp[s], new Set(bs)).set.has(e))) {
        const pushes = [];
        for (let t = s; t > 0; t = parent[t]) pushes.push({ from: pfrom[t], dir: pdir[t] });
        pushes.reverse();
        return replay(c, startPlayer, b0, pushes);
      }
    }
    expanded++;
    const boxSet = new Set(bs), reg = region(c, sp[s], boxSet);
    for (let i = 0; i < n; i++) {
      const b = bs[i];
      for (let k = 0; k < 4; k++) {
        const behind = b - (DY[k] * w + DX[k]), target = b + DY[k] * w + DX[k];
        if (!reg.set.has(behind)) continue;
        if (!F.has(target) || boxSet.has(target)) continue;
        const nb2 = bs.slice();
        nb2[i] = target; nb2.sort((a, b) => a - b);
        if (dead(c, nb2)) continue;
        const hh = h(nb2);
        if (!isFinite(hh)) continue;
        const rep2 = region(c, b, new Set(nb2)).rep, k2 = keyOf(rep2, nb2), seen = best.get(k2);
        if (seen !== undefined && sg[seen] <= g + 1) continue;
        const t = add(rep2, nb2, g + 1, s, b, k);
        push([g + 1 + hh, g + 1, seq++, t]);
      }
    }
  }
  return null;
}
function ida(c, startPlayer, boxes0, exitCells, exitReq, budget) {
  const { w, goalSet } = c, n = boxes0.length, h = heur(c);
  let nodes = 0, found = null;
  const b0 = boxes0.slice().sort((a, b) => a - b);
  const dfs = (rep, bs, g, bound, path, onPath) => {
    if (found) return -1;
    if (++nodes > budget) return Infinity;
    const f = g + h(bs);
    if (f > bound) return f;
    if (bs.every((b) => goalSet.has(b))) {
      if (!exitReq || exitCells.some((e) => region(c, rep, new Set(bs)).set.has(e))) {
        found = path.slice(); return -1;
      }
    }
    const boxSet = new Set(bs), reg = region(c, rep, boxSet);
    let next = Infinity;
    for (let i = 0; i < n; i++) {
      const b = bs[i];
      for (let k = 0; k < 4; k++) {
        const behind = b - (DY[k] * w + DX[k]), target = b + DY[k] * w + DX[k];
        if (!reg.set.has(behind)) continue;
        if (!c.F.has(target) || boxSet.has(target)) continue;
        const nb2 = bs.slice();
        nb2[i] = target; nb2.sort((a, b) => a - b);
        if (dead(c, nb2)) continue;
        const rep2 = region(c, b, new Set(nb2)).rep, k2 = keyOf(rep2, nb2);
        if (onPath.has(k2)) continue;
        onPath.add(k2); path.push({ from: b, dir: k });
        const r = dfs(rep2, nb2, g + 1, bound, path, onPath);
        path.pop(); onPath.delete(k2);
        if (found) return -1;
        if (r < next) next = r;
      }
    }
    return next;
  };
  const h0 = h(b0);
  if (!isFinite(h0) || dead(c, b0)) return null;
  const rep0 = region(c, startPlayer, new Set(b0)).rep;
  let bound = h0;
  const onPath = new Set([keyOf(rep0, b0)]);
  while (bound !== Infinity && nodes <= budget) {
    const r = dfs(rep0, b0, 0, bound, [], onPath);
    if (found) break;
    if (r === Infinity) return null;
    bound = r;
  }
  if (!found) return null;
  return replay(c, startPlayer, b0, found);
}
function room(c, entry, boxes, exitCells, exitReq, budget) {
  return astar(c, entry, boxes, exitCells, exitReq, budget)
    ?? ida(c, entry, boxes, exitCells, exitReq, budget * 2);
}
function splitSolve(g, dec) {
  const infos = [];
  for (const r of dec.rooms) {
    const floor = new Set(r.cells);
    for (const e of r.entries) floor.add(e);
    const c = ctx(g, floor, r.goals);
    const sol = room(c, r.entries[0], r.boxes, r.entries, false, RB);
    if (!sol) return null;
    const exitOk = region(c, sol.finalPlayer, new Set(sol.finalBoxes)).set.has(r.entries[0]);
    infos.push({ room: r, c, sol, exitOk, delta: 0 });
  }
  let last = -1;
  for (let i = 0; i < infos.length; i++) {
    if (infos[i].exitOk) continue;
    const inf = infos[i];
    const sol2 = room(inf.c, inf.room.entries[0], inf.room.boxes, inf.room.entries, true, EB);
    if (sol2) { inf.delta = sol2.pushes - inf.sol.pushes; inf.sol = sol2; inf.exitOk = true; }
    else if (last === -1) last = i;
    else return null;
  }
  if (last === -1) {
    last = infos.length - 1;
    for (let i = 0; i < infos.length; i++) if (infos[i].delta > infos[last].delta) last = i;
  }
  const order = infos.map((_, i) => i).filter((i) => i !== last);
  order.push(last);
  let moves = '', player = g.player;
  const boxes = g.boxes.slice();
  for (let oi = 0; oi < order.length; oi++) {
    const inf = infos[order[oi]], entry = inf.room.entries[0];
    const hallCtx = { w: g.w, h: g.h, F: dec.hall };
    const allCtx = { w: g.w, h: g.h, F: new Set([...Array(g.w * g.h).keys()].filter((x) => !g.wall[x])) };
    const path = walk(hallCtx, player, entry, new Set(boxes)) ?? walk(allCtx, player, entry, new Set(boxes));
    if (path === null) return null;
    moves += path; player = entry; moves += inf.sol.moves; player = inf.sol.finalPlayer;
    for (const b of inf.room.boxes) {
      const bi = boxes.indexOf(b);
      if (bi >= 0) boxes.splice(bi, 1);
    }
    for (const b of inf.sol.finalBoxes) boxes.push(b);
    boxes.sort((a, b) => a - b);
    if (oi < order.length - 1) {
      const exit = walk(inf.c, player, entry, new Set(inf.sol.finalBoxes));
      if (exit === null) return null;
      moves += exit; player = entry;
    }
  }
  return moves;
}
function solve(t) {
  const g = parse(t), dec = split(g);
  if (dec) {
    const m = splitSolve(g, dec);
    if (m !== null) return m;
  }
  const floor = new Set();
  for (let i = 0; i < g.w * g.h; i++) if (!g.wall[i]) floor.add(i);
  const c = ctx(g, floor, g.goals), sol = room(c, g.player, g.boxes, [], false, GB);
  return sol ? sol.moves : '';
}
for (const id of readdirSync(I).sort()) {
  const moves = solve(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
