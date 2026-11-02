/* =====================================================================
   NEBULA LEDGER
   Part 1: ENGINE  – the "backend". Pure logic, no DOM access.
   Part 2: UI      – forms, lists, toasts.
   Part 3: COSMOS  – canvas constellation renderer.
   ===================================================================== */

/* ---------------------------------------------------------------------
   PART 1: ENGINE
   An append-only, hash-chained ledger. Money is kept in integer cents
   so there are never floating-point rounding errors.
--------------------------------------------------------------------- */
const Engine = (() => {
  const KEY = 'nebula-ledger-v1';
  const PALETTE = ['#5fd4ff','#ffa24a','#c79bff','#7ef0c6','#ff7ab8','#ffd36e','#8fb4ff','#ff9b6a'];
  let entries = [];

  /* ----- hashing (SHA-256, with a tiny fallback for non-secure contexts) ----- */
  const enc = new TextEncoder();
  async function sha(str) {
    const subtle = window.crypto && window.crypto.subtle;
    if (subtle) {
      const buf = await subtle.digest('SHA-256', enc.encode(str));
      return [...new Uint8Array(buf)].map(b => b.toString(16).padStart(2, '0')).join('');
    }
    let h1 = 0xdeadbeef, h2 = 0x41c6ce57;           // cyrb53 fallback
    for (let i = 0; i < str.length; i++) {
      const c = str.charCodeAt(i);
      h1 = Math.imul(h1 ^ c, 2654435761); h2 = Math.imul(h2 ^ c, 1597334677);
    }
    h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507) ^ Math.imul(h2 ^ (h2 >>> 13), 3266489909);
    h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507) ^ Math.imul(h1 ^ (h1 >>> 13), 3266489909);
    return (4294967296 * (2097151 & h2) + (h1 >>> 0)).toString(16).padStart(16, '0');
  }
  const bodyOf = e => JSON.stringify({ i: e.i, t: e.t, type: e.type, data: e.data, prev: e.prev });

  /* ----- persistence ----- */
  const save = () => { try { localStorage.setItem(KEY, JSON.stringify(entries)); } catch (_) {} };
  const load = () => { try { entries = JSON.parse(localStorage.getItem(KEY)) || []; } catch (_) { entries = []; } };

  /* ----- the one and only way to write: append ----- */
  async function append(type, data) {
    const prev = entries.length ? entries[entries.length - 1].hash : 'GENESIS';
    const e = { i: entries.length, t: Date.now(), type, data, prev };
    e.hash = await sha(bodyOf(e));
    entries.push(e);
    save();
    return e;
  }

  /* ----- verify the whole chain; returns index of first broken block or -1 ----- */
  async function verify(list = entries) {
    let prev = 'GENESIS';
    for (let k = 0; k < list.length; k++) {
      const e = list[k];
      if (e.prev !== prev || e.i !== k || (await sha(bodyOf(e))) !== e.hash) return k;
      prev = e.hash;
    }
    return -1;
  }

  /* ----- split maths: largest-remainder so shares always add to the cent ----- */
  function proportional(amount, weights) {         // weights: {id: number}
    const ids = Object.keys(weights);
    const total = ids.reduce((s, id) => s + weights[id], 0);
    if (!ids.length || total <= 0) throw new Error('Pick at least one person with a share.');
    const raw = ids.map(id => ({ id, v: amount * weights[id] / total }));
    const out = {}; let used = 0;
    raw.forEach(r => { out[r.id] = Math.floor(r.v); used += out[r.id]; });
    raw.sort((a, b) => (b.v - Math.floor(b.v)) - (a.v - Math.floor(a.v)));
    for (let k = 0; k < amount - used; k++) out[raw[k % raw.length].id]++;
    return out;
  }
  function computeShares(amount, mode, values) {   // values: {id: number}
    const ids = Object.keys(values);
    if (!ids.length) throw new Error('Pick at least one person to split with.');
    if (mode === 'equal') return proportional(amount, Object.fromEntries(ids.map(i => [i, 1])));
    if (mode === 'shares') return proportional(amount, values);
    if (mode === 'percent') {
      const sum = ids.reduce((s, i) => s + values[i], 0);
      if (Math.abs(sum - 100) > 0.001) throw new Error(`Percentages add up to ${+sum.toFixed(2)}%, not 100%.`);
      return proportional(amount, values);
    }
    if (mode === 'exact') {
      const cents = Object.fromEntries(ids.map(i => [i, Math.round(values[i] * 100)]));
      const sum = ids.reduce((s, i) => s + cents[i], 0);
      if (sum !== amount) throw new Error('Exact amounts must add up to the full bill.');
      return cents;
    }
    throw new Error('Unknown split mode');
  }

  /* ----- replay the chain into a live state ----- */
  function state() {
    const voided = new Set(entries.filter(e => e.type === 'void').map(e => e.data.ref));
    const people = [], bal = {}, pair = {};
    let total = 0;
    const bump = (debtor, creditor, amt) => {       // debtor owes creditor amt
      const k = debtor < creditor ? debtor + '|' + creditor : creditor + '|' + debtor;
      pair[k] = (pair[k] || 0) + (debtor < creditor ? amt : -amt);
    };
    entries.forEach(e => {
      if (e.type === 'join') {
        people.push({ id: e.data.id, name: e.data.name, color: PALETTE[people.length % PALETTE.length] });
        bal[e.data.id] = 0;
      }
      if (voided.has(e.i)) return;
      if (e.type === 'expense') {
        const d = e.data; total += d.amount;
        bal[d.payer] += d.amount;
        Object.entries(d.shares).forEach(([id, s]) => { bal[id] -= s; if (id !== d.payer) bump(id, d.payer, s); });
      }
      if (e.type === 'settle') {
        const d = e.data;
        bal[d.from] += d.amount; bal[d.to] -= d.amount;
        bump(d.to, d.from, d.amount);               // paying down debt
      }
    });
    const plan = simplify(bal);
    const naive = Object.values(pair).filter(v => v !== 0).length;
    return { people, bal, plan, total, voided, naive, entries };
  }

  /* ----- min-cash-flow: greedy match biggest debtor with biggest creditor ----- */
  function simplify(bal) {
    const cr = [], db = [];
    Object.entries(bal).forEach(([id, v]) => { if (v > 0) cr.push({ id, v }); else if (v < 0) db.push({ id, v: -v }); });
    const plan = [];
    while (cr.length && db.length) {
      cr.sort((a, b) => b.v - a.v); db.sort((a, b) => b.v - a.v);
      const c = cr[0], d = db[0], amt = Math.min(c.v, d.v);
      plan.push({ from: d.id, to: c.id, amount: amt });
      c.v -= amt; d.v -= amt;
      if (c.v === 0) cr.shift();
      if (d.v === 0) db.shift();
    }
    return plan;
  }

  /* ----- extras ----- */
  const uid = () => 'p' + Math.random().toString(36).slice(2, 8);
  const exportJSON = () => JSON.stringify(entries, null, 2);
  async function importJSON(text) {
    const list = JSON.parse(text);
    if (!Array.isArray(list)) throw new Error('That file is not a ledger.');
    const bad = await verify(list);
    if (bad !== -1) throw new Error(`Import rejected: entry #${bad} fails its hash check.`);
    entries = list; save();
  }
  const reset = () => { entries = []; save(); };
  const tamper = () => {                            // in-memory only, to demo the chain
    const t = entries.find(e => e.type === 'expense');
    if (!t) return false;
    t.data.amount = Math.max(1, Math.floor(t.data.amount / 2));
    return true;
  };

  load();
  return { append, verify, state, computeShares, uid, exportJSON, importJSON, reset, tamper, reload: load, get entries() { return entries; } };
})();


/* ---------------------------------------------------------------------
   PART 2: UI
--------------------------------------------------------------------- */
const $ = (s, r = document) => r.querySelector(s);
let S = null;                    // latest derived state
let mode = 'equal';
let currency = '₹';
let brokenAt = -1;

const money = c => currency + (c / 100).toLocaleString('en-IN', { minimumFractionDigits: 2, maximumFractionDigits: 2 });
const nameOf = id => (S.people.find(p => p.id === id) || { name: '?' }).name;
const colorOf = id => (S.people.find(p => p.id === id) || { color: '#fff' }).color;
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));

function toast(msg) {
  const t = $('#toast'); t.textContent = msg; t.classList.add('show');
  clearTimeout(toast.id); toast.id = setTimeout(() => t.classList.remove('show'), 2400);
}

async function refresh() {
  S = Engine.state();
  brokenAt = await Engine.verify();
  renderBadge(); renderCrew(); renderPayer(); renderSplitRows(); renderPlan(); renderChain(); renderStats();
  Cosmos.sync(S);
}

function renderBadge() {
  const b = $('#badge'), n = Engine.entries.length;
  if (brokenAt === -1) { b.classList.remove('broken'); $('#badgeText').textContent = n ? `Chain verified (${n} entries)` : 'Chain empty'; $('#healBtn').hidden = true; }
  else { b.classList.add('broken'); $('#badgeText').textContent = `Tampering found at entry #${brokenAt}`; $('#healBtn').hidden = false; }
}

function renderCrew() {
  $('#crewCount').textContent = S.people.length ? `${S.people.length} aboard` : '';
  $('#crewList').innerHTML = S.people.length ? S.people.map(p => {
    const v = S.bal[p.id], cls = v > 0 ? 'pos' : v < 0 ? 'neg' : 'zero';
    const label = v > 0 ? `gets ${money(v)}` : v < 0 ? `owes ${money(-v)}` : 'settled';
    return `<div class="person"><span class="dot" style="color:${p.color}"></span><b>${esc(p.name)}</b><span class="bal ${cls}">${label}</span></div>`;
  }).join('') : `<div class="empty">Nobody here yet. Add the people who are splitting bills.</div>`;
}

function renderPayer() {
  const sel = $('#payer'), keep = sel.value;
  sel.innerHTML = S.people.map(p => `<option value="${p.id}">${esc(p.name)}</option>`).join('');
  if (S.people.some(p => p.id === keep)) sel.value = keep;
}

/* The per-person split rows. Rebuilt only when people/mode change so typed values survive. */
function renderSplitRows() {
  const box = $('#splitRows');
  const sig = mode + '|' + S.people.map(p => p.id).join(',');
  if (box.dataset.sig === sig) { updatePreview(); return; }
  box.dataset.sig = sig;
  const ph = { equal: '', exact: '0.00', percent: '%', shares: '1' }[mode];
  box.innerHTML = S.people.map(p => `
    <div class="split-row" data-id="${p.id}">
      <input type="checkbox" checked aria-label="Include ${esc(p.name)}">
      <span><span class="dot" style="color:${p.color};display:inline-block;margin-right:8px;width:10px;height:10px"></span>${esc(p.name)}</span>
      ${mode === 'equal' ? `<span class="share-out"></span>` : `<input type="number" min="0" step="any" placeholder="${ph}" ${mode === 'shares' ? 'value="1"' : ''}>`}
    </div>`).join('') || `<div class="empty">Add people first.</div>`;
  updatePreview();
}

/* Read the form → {id: number}. Equal mode just needs ids. */
function readSplit() {
  const out = {};
  document.querySelectorAll('#splitRows .split-row').forEach(r => {
    if (!r.querySelector('input[type=checkbox]').checked) return;
    const num = r.querySelector('input[type=number]');
    out[r.dataset.id] = mode === 'equal' ? 1 : (parseFloat(num.value) || 0);
  });
  if (mode !== 'equal') Object.keys(out).forEach(k => { if (out[k] <= 0) delete out[k]; });
  return out;
}

function updatePreview() {
  const hint = $('#splitHint'); hint.classList.remove('err'); hint.textContent = '';
  document.querySelectorAll('#splitRows .share-out').forEach(e => e.textContent = '');
  const amt = Math.round((parseFloat($('#amount').value) || 0) * 100);
  const vals = readSplit();
  if (mode === 'percent') { const s = Object.values(vals).reduce((a, b) => a + b, 0); hint.textContent = `Total: ${+s.toFixed(2)}% of 100%`; }
  if (mode === 'exact') { const s = Object.values(vals).reduce((a, b) => a + b, 0); hint.textContent = `Assigned ${money(Math.round(s * 100))} of ${money(amt)}`; }
  if (amt <= 0) return;
  try {
    const sh = Engine.computeShares(amt, mode, vals);
    if (mode === 'equal') document.querySelectorAll('#splitRows .split-row').forEach(r => {
      const o = r.querySelector('.share-out'); if (o && sh[r.dataset.id] != null) o.textContent = money(sh[r.dataset.id]);
    });
    else if (mode === 'shares' || mode === 'percent') hint.textContent += (hint.textContent ? ' | ' : '') + Object.entries(sh).map(([id, c]) => `${nameOf(id)} ${money(c)}`).join(', ');
  } catch (_) { /* hints only; real errors surface on submit */ }
}

function renderPlan() {
  const box = $('#planList');
  if (!S.people.length) { box.innerHTML = `<div class="empty">Add people and an expense to see who pays whom.</div>`; return; }
  if (!S.plan.length) { box.innerHTML = `<div class="empty">${S.total ? 'Everyone is square. Nothing left to pay.' : 'No expenses yet.'}</div>`; return; }
  box.innerHTML = S.plan.map((t, i) => `
    <div class="transfer" style="border-left-color:${colorOf(t.from)}">
      <div class="who">
        <b style="color:${colorOf(t.from)}">${esc(nameOf(t.from))}</b><span class="arrow">pays</span>
        <b style="color:${colorOf(t.to)}">${esc(nameOf(t.to))}</b><span class="amt">${money(t.amount)}</span>
      </div>
      <button class="btn warm tiny" data-settle="${i}">Mark paid</button>
    </div>`).join('');
}

function renderStats() {
  $('#sTotal').textContent = money(S.total);
  $('#sPlan').textContent = S.plan.length;
  $('#sSaved').textContent = Math.max(0, S.naive - S.plan.length);
}

function describe(e) {
  const d = e.data;
  switch (e.type) {
    case 'join': return `${esc(d.name)} joined the crew`;
    case 'expense': return `${esc(d.desc)} – ${money(d.amount)}, paid by ${esc(nameOf(d.payer))}`;
    case 'settle': return `${esc(nameOf(d.from))} paid ${esc(nameOf(d.to))} ${money(d.amount)}`;
    case 'void': return `Cancelled entry #${d.ref}`;
  }
}
function renderChain() {
  const list = Engine.entries;
  $('#chainCount').textContent = list.length ? `${list.length} linked` : '';
  if (!list.length) { $('#blocks').innerHTML = `<div class="empty">The chain starts with the first person you add.</div>`; return; }
  $('#blocks').innerHTML = [...list].reverse().map(e => {
    const voided = S.voided.has(e.i), canVoid = (e.type === 'expense' || e.type === 'settle') && !voided;
    const time = new Date(e.t).toLocaleString([], { day: 'numeric', month: 'short', hour: '2-digit', minute: '2-digit' });
    return `<div class="block ${e.type} ${voided ? 'voided' : ''} ${brokenAt !== -1 && e.i >= brokenAt ? 'bad' : ''}">
      <div class="top"><span class="what">${describe(e)}</span><span class="when">${time}</span></div>
      <div class="meta"><span>#${e.i}</span><span>hash <em>${e.hash.slice(0, 10)}</em></span><span>prev <em>${e.prev === 'GENESIS' ? 'genesis' : e.prev.slice(0, 10)}</em></span>
      ${canVoid ? `<button class="btn tiny danger" data-void="${e.i}">Cancel</button>` : ''}</div>
    </div>`;
  }).join('');
}

/* ---------- actions ---------- */
async function addPerson() {
  const el = $('#newName'), name = el.value.trim();
  if (!name) return toast('Type a name first.');
  if (S.people.some(p => p.name.toLowerCase() === name.toLowerCase())) return toast(`${name} is already aboard.`);
  await Engine.append('join', { id: Engine.uid(), name });
  el.value = ''; el.focus(); await refresh();
}

async function addExpense() {
  const desc = $('#desc').value.trim(), amount = Math.round((parseFloat($('#amount').value) || 0) * 100), payer = $('#payer').value;
  const hint = $('#splitHint');
  try {
    if (S.people.length < 2) throw new Error('Add at least two people.');
    if (!desc) throw new Error('Describe the expense.');
    if (amount <= 0) throw new Error('Enter an amount above zero.');
    const shares = Engine.computeShares(amount, mode, readSplit());
    await Engine.append('expense', { desc, amount, payer, mode, shares });
    $('#desc').value = ''; $('#amount').value = '';
    toast('Expense added to the chain.'); await refresh();
  } catch (err) { hint.textContent = err.message; hint.classList.add('err'); }
}

async function loadDemo() {
  const crew = ['Aarav', 'Meera', 'Kabir', 'Isha'].map(n => ({ id: Engine.uid(), name: n }));
  for (const c of crew) await Engine.append('join', c);
  const [a, m, k, i] = crew.map(c => c.id);
  const eq = (amt, ids) => Engine.computeShares(amt, 'equal', Object.fromEntries(ids.map(x => [x, 1])));
  await Engine.append('expense', { desc: 'Beach villa', amount: 2400000, payer: a, mode: 'equal', shares: eq(2400000, [a, m, k, i]) });
  await Engine.append('expense', { desc: 'Seafood dinner', amount: 468000, payer: m, mode: 'equal', shares: eq(468000, [a, m, k]) });
  await Engine.append('expense', { desc: 'Scooter rental', amount: 180000, payer: k, mode: 'shares', shares: Engine.computeShares(180000, 'shares', { [a]: 1, [m]: 1, [k]: 2, [i]: 1 }) });
  await Engine.append('expense', { desc: 'Sunset cruise', amount: 360000, payer: i, mode: 'percent', shares: Engine.computeShares(360000, 'percent', { [a]: 20, [m]: 20, [k]: 30, [i]: 30 }) });
  toast('Demo trip loaded.'); await refresh();
}

/* ---------- wiring ---------- */
$('#addPerson').onclick = addPerson;
$('#newName').addEventListener('keydown', e => e.key === 'Enter' && addPerson());
$('#addExpense').onclick = addExpense;
$('#amount').addEventListener('input', updatePreview);
$('#splitRows').addEventListener('input', updatePreview);
$('#splitRows').addEventListener('change', updatePreview);
$('#cur').addEventListener('input', e => { currency = e.target.value || '₹'; refresh(); });
$('#demoBtn').onclick = async () => { if (Engine.entries.length && !confirm('This adds demo people on top of your current ledger. Continue?')) return; loadDemo(); };

$('#seg').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  mode = b.dataset.mode;
  document.querySelectorAll('#seg button').forEach(x => x.setAttribute('aria-pressed', x === b));
  renderSplitRows();
});

$('#planList').addEventListener('click', async e => {
  const b = e.target.closest('[data-settle]'); if (!b) return;
  const t = S.plan[+b.dataset.settle];
  await Engine.append('settle', { from: t.from, to: t.to, amount: t.amount });
  toast(`${nameOf(t.from)} paid ${nameOf(t.to)}.`); refresh();
});

$('#blocks').addEventListener('click', async e => {
  const b = e.target.closest('[data-void]'); if (!b) return;
  await Engine.append('void', { ref: +b.dataset.void });
  toast('Entry cancelled. The original stays on the chain.'); refresh();
});

$('#tamperBtn').onclick = async () => {
  if (!Engine.tamper()) return toast('Add an expense first, then try to cheat it.');
  await refresh(); toast('You edited an old entry. The chain noticed.');
};
$('#healBtn').onclick = async () => { Engine.reload(); await refresh(); toast('Restored the saved ledger.'); };

$('#exportBtn').onclick = () => {
  const a = document.createElement('a');
  a.href = URL.createObjectURL(new Blob([Engine.exportJSON()], { type: 'application/json' }));
  a.download = 'nebula-ledger.json'; a.click(); URL.revokeObjectURL(a.href);
};
$('#importBtn').onclick = () => $('#importFile').click();
$('#importFile').onchange = async e => {
  const f = e.target.files[0]; if (!f) return;
  try { await Engine.importJSON(await f.text()); toast('Ledger imported and verified.'); refresh(); }
  catch (err) { toast(err.message); }
  e.target.value = '';
};
$('#resetBtn').onclick = () => { if (confirm('Erase the whole ledger? Export it first if you need a copy.')) { Engine.reset(); refresh(); } };


/* ---------------------------------------------------------------------
   PART 3: COSMOS – constellation canvas
   People are planets (size = how much they owe or are owed),
   settle-up payments are comets flowing from debtor to creditor.
--------------------------------------------------------------------- */
const Cosmos = (() => {
  const cv = $('#cosmos'), cx = cv.getContext('2d'), tip = $('#tip');
  const reduce = matchMedia('(prefers-reduced-motion: reduce)').matches;
  let W = 0, H = 0, state = null, nodes = [], hover = null, stars = [];

  for (let i = 0; i < 160; i++) stars.push({ x: Math.random(), y: Math.random(), r: Math.random() * 1.4 + .3, p: Math.random() * 6.28 });

  function resize() {
    const r = cv.getBoundingClientRect(), dpr = Math.min(window.devicePixelRatio || 1, 2);
    W = r.width; H = r.height; cv.width = W * dpr; cv.height = H * dpr; cx.setTransform(dpr, 0, 0, dpr, 0, 0);
  }
  addEventListener('resize', resize);

  const bez = (a, c, b, t) => ({
    x: (1 - t) * (1 - t) * a.x + 2 * (1 - t) * t * c.x + t * t * b.x,
    y: (1 - t) * (1 - t) * a.y + 2 * (1 - t) * t * c.y + t * t * b.y
  });

  function sync(s) { state = s; }

  function frame(ms) {
    const t = reduce ? 0 : ms;
    cx.clearRect(0, 0, W, H);
    const bg = cx.createRadialGradient(W / 2, H / 2, 20, W / 2, H / 2, Math.max(W, H) * .7);
    bg.addColorStop(0, '#1a2054'); bg.addColorStop(1, '#0a0d22');
    cx.fillStyle = bg; cx.fillRect(0, 0, W, H);
    stars.forEach(s => {
      cx.globalAlpha = .35 + .65 * Math.abs(Math.sin(t * .0007 + s.p));
      cx.fillStyle = '#dfe4ff'; cx.beginPath(); cx.arc(s.x * W, s.y * H, s.r, 0, 6.283); cx.fill();
    });
    cx.globalAlpha = 1;

    if (!state || !state.people.length) {
      cx.fillStyle = '#9aa0d6'; cx.font = '600 16px "Bricolage Grotesque",sans-serif'; cx.textAlign = 'center';
      cx.fillText('Your constellation appears here once people join.', W / 2, H / 2); requestAnimationFrame(frame); return;
    }

    /* layout */
    const n = state.people.length, R = Math.min(W * .36, H * .34), maxAbs = Math.max(1, ...Object.values(state.bal).map(Math.abs));
    nodes = state.people.map((p, i) => {
      const a = (i / n) * 6.283 - 1.5708 + t * .00004;
      const x = n === 1 ? W / 2 : W / 2 + Math.cos(a) * R * 1.2 + Math.sin(t * .0009 + i * 2) * 5;
      const y = n === 1 ? H / 2 : H / 2 + Math.sin(a) * R + Math.cos(t * .0008 + i) * 5;
      const v = state.bal[p.id];
      return { p, x, y, v, r: 17 + 24 * Math.min(1, Math.abs(v) / maxAbs) };
    });
    const byId = Object.fromEntries(nodes.map(nd => [nd.p.id, nd]));

    /* orbit ring */
    cx.strokeStyle = '#ffffff10'; cx.lineWidth = 1; cx.beginPath(); cx.ellipse(W / 2, H / 2, R * 1.2, R, 0, 0, 6.283); cx.stroke();

    /* debt comets */
    const maxAmt = Math.max(1, ...state.plan.map(x => x.amount));
    state.plan.forEach((tr, k) => {
      const a = byId[tr.from], b = byId[tr.to]; if (!a || !b) return;
      const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
      const c = { x: mx + (W / 2 - mx) * .45, y: my + (H / 2 - my) * .45 };
      const w = 1.5 + 4 * tr.amount / maxAmt;
      const g = cx.createLinearGradient(a.x, a.y, b.x, b.y); g.addColorStop(0, '#ffa24a99'); g.addColorStop(1, '#5fd4ff99');
      cx.strokeStyle = g; cx.lineWidth = w; cx.beginPath(); cx.moveTo(a.x, a.y); cx.quadraticCurveTo(c.x, c.y, b.x, b.y); cx.stroke();
      for (let q = 0; q < 7; q++) {
        const u = ((t * .00022 + q / 7 + k * .13) % 1);
        const pt = bez(a, c, b, u);
        cx.fillStyle = `rgba(255,255,255,${.25 + .75 * Math.sin(u * 3.14)})`;
        cx.beginPath(); cx.arc(pt.x, pt.y, w * .7 + .6, 0, 6.283); cx.fill();
      }
      const lab = bez(a, c, b, .5);
      cx.fillStyle = '#f2eeff'; cx.font = '500 12px "IBM Plex Mono",monospace'; cx.textAlign = 'center';
      cx.fillText(money(tr.amount), lab.x, lab.y - 8);
    });

    /* planets */
    nodes.forEach(nd => {
      const col = nd.p.color, hot = hover === nd.p.id;
      const ring = nd.v > 0 ? '#5fd4ff' : nd.v < 0 ? '#ffa24a' : '#7ef0c6';
      const glow = cx.createRadialGradient(nd.x, nd.y, nd.r * .4, nd.x, nd.y, nd.r * 2.6);
      glow.addColorStop(0, ring + (hot ? 'aa' : '55')); glow.addColorStop(1, ring + '00');
      cx.fillStyle = glow; cx.beginPath(); cx.arc(nd.x, nd.y, nd.r * 2.6, 0, 6.283); cx.fill();
      const body = cx.createRadialGradient(nd.x - nd.r * .35, nd.y - nd.r * .4, 2, nd.x, nd.y, nd.r);
      body.addColorStop(0, '#ffffff'); body.addColorStop(.25, col); body.addColorStop(1, '#101544');
      cx.fillStyle = body; cx.beginPath(); cx.arc(nd.x, nd.y, nd.r, 0, 6.283); cx.fill();
      cx.strokeStyle = ring; cx.lineWidth = 2; cx.beginPath(); cx.arc(nd.x, nd.y, nd.r + 4, 0, 6.283); cx.stroke();
      cx.fillStyle = '#f2eeff'; cx.textAlign = 'center';
      cx.font = '600 14px "Bricolage Grotesque",sans-serif'; cx.fillText(nd.p.name, nd.x, nd.y + nd.r + 22);
      cx.font = '500 11px "IBM Plex Mono",monospace'; cx.fillStyle = ring;
      cx.fillText(nd.v === 0 ? 'settled' : (nd.v > 0 ? '+' : '-') + money(Math.abs(nd.v)), nd.x, nd.y + nd.r + 38);
    });

    if (!state.plan.length && state.total > 0) {
      cx.fillStyle = '#7ef0c6'; cx.font = '800 22px "Bricolage Grotesque",sans-serif'; cx.textAlign = 'center';
      cx.fillText('All square', W / 2, H / 2 + 6);
    }
    requestAnimationFrame(frame);
  }

  /* hover tooltip */
  cv.addEventListener('mousemove', e => {
    const r = cv.getBoundingClientRect(), mx = e.clientX - r.left, my = e.clientY - r.top;
    const hit = nodes.find(nd => Math.hypot(nd.x - mx, nd.y - my) < nd.r + 8);
    hover = hit ? hit.p.id : null;
    if (hit) {
      tip.style.opacity = 1; tip.style.left = (mx + 14) + 'px'; tip.style.top = (my + 14) + 'px';
      tip.textContent = `${hit.p.name}: ${hit.v > 0 ? 'is owed ' + money(hit.v) : hit.v < 0 ? 'owes ' + money(-hit.v) : 'is settled'}`;
    } else tip.style.opacity = 0;
  });
  cv.addEventListener('mouseleave', () => { hover = null; tip.style.opacity = 0; });

  resize(); requestAnimationFrame(frame);
  return { sync, resize };
})();

/* ---------- boot ---------- */
refresh().then(() => Cosmos.resize());
