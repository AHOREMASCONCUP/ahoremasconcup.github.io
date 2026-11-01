// Admin jobs run from GitHub Actions with the service-account key (bypasses app rules).
// ACTION=real-setup : wipe demo data (matches, polls, fantasy, fans, lock) and write
//                     the 10 franchises with icons + 20 league fixtures.
import fs from "node:fs";
import vm from "node:vm";
import { GoogleAuth } from "google-auth-library";

const project = "ahore-mascon-cup-2026";
const ACTION = process.env.ACTION || "";
let key = process.env.KEY || "";
if (!key.trim().startsWith("{")) key = "{" + key;
const auth = new GoogleAuth({ credentials: JSON.parse(key), scopes: ["https://www.googleapis.com/auth/datastore", "https://www.googleapis.com/auth/cloud-platform"] });
const client = await auth.getClient();
const root = `projects/${project}/databases/(default)/documents`;
const api = `https://firestore.googleapis.com/v1/${root}`;
const call = async (method, url, data) => (await client.request({ method, url, data }).catch(e => { throw new Error(`${method} ${url} -> ${e.response?.status} ${JSON.stringify(e.response?.data?.error?.message || e.message)}`) })).data;

const enc = v => {
  if (v === null || v === undefined) return { nullValue: null };
  if (typeof v === "boolean") return { booleanValue: v };
  if (typeof v === "number") return Number.isInteger(v) ? { integerValue: String(v) } : { doubleValue: v };
  if (typeof v === "string") return { stringValue: v };
  if (Array.isArray(v)) return { arrayValue: { values: v.map(enc) } };
  return { mapValue: { fields: Object.fromEntries(Object.entries(v).filter(([, x]) => x !== undefined).map(([k, x]) => [k, enc(x)])) } };
};
const commit = async writes => { for (let i = 0; i < writes.length; i += 400) await call("POST", `${api}:commit`, { writes: writes.slice(i, i + 400) }); };
const listIds = async col => { const out = []; let tok = ""; do { const r = await call("GET", `${api}/${col}?pageSize=300&mask.fieldPaths=__name__${tok ? "&pageToken=" + tok : ""}`); (r.documents || []).forEach(d => out.push(d.name)); tok = r.nextPageToken || ""; } while (tok); return out; };

const ctx = { window: {} }; vm.runInNewContext(fs.readFileSync("players.js", "utf8"), ctx);
const POOL = ctx.window.MASCON_POOL, PRESET = ctx.window.MASCON_TEAMS;
const uidGen = p => p + Date.now().toString(36).slice(-4) + Math.random().toString(36).slice(2, 7);
const poolPlayer = name => { const p = POOL.find(x => x.name.toLowerCase() === name.toLowerCase()); return p ? { id: uidGen("p"), name: p.name, reg: p.reg, role: p.role, age: p.age } : { id: uidGen("p"), name }; };
function roundRobin(ids) {
  const a = [...ids]; if (a.length % 2) a.push(null); const n = a.length, rounds = [];
  for (let r = 0; r < n - 1; r++) { const g = []; for (let i = 0; i < n / 2; i++) { const x = a[i], y = a[n - 1 - i]; if (x && y) g.push(r % 2 ? [y, x] : [x, y]); } rounds.push(g); a.splice(1, 0, a.pop()); }
  return rounds;
}

if (ACTION === "real-setup") {
  const del = [];
  for (const col of ["matches", "polls", "fantasy", "fans", "meta", "tournament"]) (await listIds(col)).forEach(n => del.push({ delete: n }));
  await commit(del); console.log("deleted", del.length, "documents");
  const DEF = { name: "Ahore Mascon Cup 2026", emergingAge: 21, overs: 12, xi: 11, minXi: 9, squad: 13, wideRuns: 1, nbRuns: 1, freeHit: true, noLbw: true, noLegBye: true, ptsWin: 2, ptsTie: 1, ptsNR: 1 };
  const teams = PRESET.map(t => ({ id: uidGen("t"), name: t.name, group: t.group, players: [poolPlayer(t.icon)] }));
  const w = [{ update: { name: `${root}/tournament/main`, fields: enc({ ...DEF, teams }).mapValue.fields } }];
  const rr = { A: roundRobin(teams.filter(t => t.group === "A").map(t => t.id)), B: roundRobin(teams.filter(t => t.group === "B").map(t => t.id)) };
  let no = 0;
  for (let r = 0; r < Math.max(rr.A.length, rr.B.length); r++) for (const g of ["A", "B"]) for (const [a, b] of rr[g][r] || []) {
    const id = uidGen("m");
    w.push({ update: { name: `${root}/matches/${id}`, fields: enc({ id, no: ++no, stage: g, a, b, status: "scheduled", inn: [], result: "", winner: null, overs: 12, upd: Date.now() }).mapValue.fields } });
  }
  await commit(w); console.log("created 10 teams and", no, "fixtures");
} else if (ACTION === "kids-teams") {
  // Create the kids tournament with its 4 teams (no players, no fixtures yet). Refuses if it already exists.
  const ex = await client.request({ method: "GET", url: `${api}/ktournament/main` }).then(() => true).catch(e => { if (e.response?.status === 404) return false; throw e; });
  if (ex) { console.log("::notice title=Kids::ktournament already exists, not touched"); }
  else {
    const DEF = { name: "Ahore Mascon Cup 2026 Kids", emergingAge: 21, overs: 12, xi: 11, minXi: 9, squad: 13, wideRuns: 1, nbRuns: 1, freeHit: true, noLbw: true, noLegBye: true, ptsWin: 2, ptsTie: 1, ptsNR: 1 };
    const teams = ["TITANS", "MPC CHALLENGERS", "KOTHARI XI", "YOUNG FIGHTERS"].map(n => ({ id: uidGen("t"), name: n, group: "A", players: [] }));
    await commit([{ update: { name: `${root}/ktournament/main`, fields: enc({ ...DEF, teams }).mapValue.fields } }]);
    console.log("::notice title=Kids::created 4 kids teams");
  }
} else if (ACTION === "status") {
  const c = {}; for (const col of ["tournament", "matches", "polls", "fantasy", "fans", "meta", "ktournament", "kmatches"]) c[col] = (await listIds(col)).length;
  console.log("::notice title=Firestore counts::" + JSON.stringify(c));
} else if (ACTION === "go-live-check") {
  const note = (t, m) => console.log(`::notice title=${t}::${m}`);
  const DOMAIN = "ahoremasconcup.github.io", SITE = `https://${DOMAIN}/`;
  // 1. Authorized domains for Firebase Auth
  try {
    const cfgUrl = `https://identitytoolkit.googleapis.com/admin/v2/projects/${project}/config`;
    const cfg = await call("GET", cfgUrl);
    const doms = cfg.authorizedDomains || [];
    if (doms.includes(DOMAIN)) note("Auth domain", "already authorized: " + doms.join(", "));
    else { const r = await call("PATCH", cfgUrl + "?updateMask=authorizedDomains", { authorizedDomains: [...doms, DOMAIN] }); note("Auth domain", "ADDED. Now: " + (r.authorizedDomains || []).join(", ")); }
  } catch (e) { note("Auth domain FAILED", e.message.slice(0, 300)); }
  // 2. Live site serves the latest files
  for (const f of ["", "players.js", "config.js", "app.js"]) {
    try { const r = await fetch(SITE + f + "?t=" + Date.now()); const t = await r.text();
      note("Site " + (f || "index.html"), `${r.status} ${t.length} bytes${f === "players.js" ? " kidsSponsors=" + t.includes("MASCON_KIDS_SPONSORS") + " hundia=" + t.includes('"sponsor":"Smt Hulasi') : ""}${f === "app.js" ? " kids=" + t.includes("cup=kids") : ""}`);
    } catch (e) { note("Site " + f + " FAILED", e.message); }
  }
  // 3. Anonymous sign-in as a phone on the new site would do it (same API key, Referer = new site)
  try {
    const key = "AIzaSyBv8PYkcXsOSrNxsIkMVn-_EYo0Hrm0Yqg";
    const r = await fetch(`https://identitytoolkit.googleapis.com/v1/accounts:signUp?key=${key}`, { method: "POST", headers: { "content-type": "application/json", Referer: SITE, Origin: `https://${DOMAIN}` }, body: JSON.stringify({ returnSecureToken: true }) });
    const j = await r.json(); note("Fan sign-in from new site", r.status + " " + (j.idToken ? "OK" : JSON.stringify(j.error || j).slice(0, 200)));
    if (j.localId) await call("POST", `https://identitytoolkit.googleapis.com/v1/projects/${project}/accounts:delete`, { localId: j.localId }).catch(() => {});
  } catch (e) { note("Fan sign-in FAILED", e.message); }
} else if (ACTION === "fixtures") {
  // Official league fixtures (1 Nov 2026 schedule): replaces the league matches with these 20, in order, with time and pitch.
  // Positions A1..A5 / B1..B5 = the order of each group's teams in players.js. Only allowed before any ball is bowled.
  const tdoc = await call("GET", `${api}/tournament/main`);
  const dec = v => v.stringValue ?? (v.integerValue !== undefined ? +v.integerValue : v.doubleValue ?? v.booleanValue ?? (v.arrayValue ? (v.arrayValue.values || []).map(dec) : v.mapValue ? Object.fromEntries(Object.entries(v.mapValue.fields || {}).map(([k, x]) => [k, dec(x)])) : null));
  const teams = dec({ mapValue: { fields: tdoc.fields } }).teams;
  const pos = {}; for (const g of ["A", "B"]) PRESET.filter(t => t.group === g).forEach((t, i) => { const tm = teams.find(x => x.name.toLowerCase() === t.name.toLowerCase()); if (!tm) throw new Error("team not in DB: " + t.name); pos[g + (i + 1)] = tm.id; });
  const T1 = ["07:30", "09:10", "10:50", "12:30", "13:50"];
  const D1 = [["A1","A2","B1","B2"],["A3","A4","B3","B4"],["A5","A1","B5","B1"],["A2","A3","B2","B3"],["A4","A5","B4","B5"]];
  const D2 = [["B3","B5","A3","A5"],["B2","B4","A2","A4"],["B1","B3","A1","A3"],["B2","B5","A2","A5"],["B1","B4","A1","A4"]];
  const rows = []; [["2026-11-29", D1], ["2026-12-06", D2]].forEach(([day, D]) => D.forEach((r, i) => { rows.push([day, T1[i], r[0], r[1], "Pitch 1"]); rows.push([day, T1[i], r[2], r[3], "Pitch 2"]); }));
  const existing = await listIds("matches");
  const live = []; for (const n of existing) { const d = await call("GET", `${api}/${n.split("/documents/")[1]}`); const st = d.fields?.status?.stringValue; if (st && !["scheduled", "setup"].includes(st)) live.push(n); }
  if (live.length) throw new Error("matches already started; refusing to replace fixtures");
  const w = [...existing.map(n => ({ delete: n })), ...(await listIds("polls")).map(n => ({ delete: n }))];
  rows.forEach(([day, t, a, b, pitch], i) => { const id = uidGen("m"); w.push({ update: { name: `${root}/matches/${id}`, fields: enc({ id, no: i + 1, stage: a[0], a: pos[a], b: pos[b], status: "scheduled", inn: [], result: "", winner: null, overs: 12, when: `${day}T${t}:00+05:30`, pitch, upd: Date.now() }).mapValue.fields } }); });
  await commit(w);
  console.log(`::notice title=Fixtures::${rows.length} league matches written. M1 ${rows[0].join(" ")} … M20 ${rows[19].join(" ")}`);
} else if (ACTION === "squads") {
  // Load the auction squads (squads-adults.json) into the tournament: each team's players in auction order.
  // A player already in the team (the icon) keeps his id; everyone else gets a new id. Refused once a ball is bowled.
  const SQ = JSON.parse(fs.readFileSync(".github/workflows/squads-adults.json", "utf8"));
  const lock = await client.request({ url: `${api}/meta/lock` }).then(() => true).catch(e => { if (e.response?.status === 404) return false; throw e; });
  if (lock) throw new Error("a ball has been bowled; refusing to replace squads");
  const tdoc = await call("GET", `${api}/tournament/main`);
  const dec = v => v.stringValue ?? (v.integerValue !== undefined ? +v.integerValue : v.doubleValue ?? v.booleanValue ?? (v.arrayValue ? (v.arrayValue.values || []).map(dec) : v.mapValue ? Object.fromEntries(Object.entries(v.mapValue.fields || {}).map(([k, x]) => [k, dec(x)])) : null));
  const tour = dec({ mapValue: { fields: tdoc.fields } });
  const norm = x => String(x || "").trim().toLowerCase();
  let total = 0;
  for (const sq of SQ) {
    const tm = tour.teams.find(t => norm(t.name) === norm(sq.team)); if (!tm) throw new Error("team not found: " + sq.team);
    const old = tm.players || [];
    tm.players = sq.players.map(p => { const o = old.find(x => norm(x.name) === norm(p.name)); const r = { id: o ? o.id : uidGen("p"), name: p.name, reg: p.reg, role: p.role }; if (p.age) r.age = p.age; return r; });
    total += tm.players.length;
  }
  await call("PATCH", `${api}/tournament/main?updateMask.fieldPaths=teams`, { fields: { teams: enc(tour.teams) } });
  console.log(`::notice title=Squads::${total} players loaded into ${SQ.length} teams: ${SQ.map(s => s.team + " " + s.players.length).join(", ")}`);
} else if (ACTION === "restore") {
  // Put back records from a backup file (fetched from the backups branch into restore.json by the workflow).
  // Only overwrites the collections listed in COLS (default: teams, matches and meta, adults + kids). Never deletes anything.
  const file = JSON.parse(fs.readFileSync("restore.json", "utf8"));
  const want = (process.env.COLS || "tournament,matches,meta").split(",").map(x => x.trim()).filter(Boolean).flatMap(c => [c, "k" + c]);
  const w = []; const done = {};
  for (const col of want) { const docs = file.data?.[col]; if (!docs) continue; done[col] = 0;
    for (const [id, fields] of Object.entries(docs)) { w.push({ update: { name: `${root}/${col}/${id}`, fields } }); done[col]++; } }
  await commit(w);
  console.log(`::notice title=Restored from ${file.at}::${JSON.stringify(done)}`);
} else { console.error("Unknown ACTION", ACTION); process.exit(1); }
