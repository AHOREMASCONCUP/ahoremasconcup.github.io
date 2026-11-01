import { initializeApp } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-app.js";
import { getAuth, signInAnonymously, signInWithEmailAndPassword, signOut, onAuthStateChanged, EmailAuthProvider, reauthenticateWithCredential, updatePassword } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-auth.js";
import { initializeFirestore, getFirestore, persistentLocalCache, persistentMultipleTabManager, doc, collection, onSnapshot, setDoc, deleteDoc, getDoc, getDocs, writeBatch } from "https://www.gstatic.com/firebasejs/10.12.2/firebase-firestore.js";

/* ================= config ================= */
const CFG = window.MASCON_CONFIG || {};
// Which tournament: adults (default) or kids (?cup=kids). Kids data lives in k-prefixed collections.
const DEMO=(()=>{try{return new URLSearchParams(location.search).get("demo")==="1"}catch(e){return false}})();
const KIDS=(()=>{try{return new URLSearchParams(location.search).get("cup")==="kids"}catch(e){return false}})();
const C=n=>KIDS?"k"+n:n;
const SK=k=>KIDS?k+"-kids":k;
const POOL = (KIDS?window.MASCON_KIDS_POOL:window.MASCON_POOL) || [];
// Theme: config.js "theme" (stadium | night | pitch | charcoal); a ?theme= link overrides it for previewing
(function(){let th=CFG.theme||"stadium";try{const q=new URLSearchParams(location.search).get("theme");if(q)th=q}catch(e){}
  if(th!=="stadium")document.documentElement.classList.add("th-"+th)})();
const KSP = window.MASCON_KIDS_SPONSORS || {};
const PRESET = (KIDS?window.MASCON_KIDS_TEAMS:window.MASCON_TEAMS) || [];
const DEF={name:KIDS?"Ahore Mascon Cup 2026 Kids":"Ahore Mascon Cup 2026",emergingAge:21,overs:12,xi:11,minXi:9,squad:13,wideRuns:1,nbRuns:1,freeHit:true,noLbw:true,noLegBye:true,ptsWin:2,ptsTie:1,ptsNR:1,teams:[]};
const STAGES={A:"Group A",B:"Group B",QF1:"Quarter-final 1",QF2:"Quarter-final 2",SF1:"Semi-final 1",SF2:"Semi-final 2",F:"Final"};
const isLeague=m=>m.stage==="A"||m.stage==="B";
const LIVE=["live","break","super","setup"];

let T=null,M={},db=null,auth=null,uid=null,canScore=false,loaded={t:false,m:false},fatal="";
let ui={tab:"live",sel:null,scoreSel:null,sheet:null,draft:null,nm:null,toss:null,stat:"mvp",fopen:null,loginErr:"",busyLogin:false};
let pendingConfirm=null,renderDeferred=false,syncState={c:"sync",t:""};
const polls={};
let fantasyLockWritten=false;
let FAN={name:null,all:null,polls:null,at:0};
try{FAN.name=localStorage.getItem("mc-fan")||null}catch(e){}
let FT={mine:null,myId:null,all:null,allAt:0,draft:null,q:"",err:""};
try{FT.myId=localStorage.getItem(SK("mc-fid"))||null}catch(e){}
try{const h=location.hash.slice(1);if(["live","matches","table","stats","fantasy","rules"].includes(h))ui.tab=h}catch(e){}
try{const s=sessionStorage.getItem(SK("mc-score"));if(s)ui.scoreSel=s}catch(e){}

/* ================= helpers ================= */
const $=s=>document.querySelector(s);
const esc=s=>String(s??"").replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const uidGen=p=>p+Date.now().toString(36).slice(-4)+Math.random().toString(36).slice(2,7);
const clone=o=>JSON.parse(JSON.stringify(o));
const last=a=>a[a.length-1];
const teamOf=id=>(T?.teams||[]).find(t=>t.id===id);
const tname=id=>teamOf(id)?.name||"TBD";
function pname(id){if(!id)return"—";for(const t of T?.teams||[]){const p=t.players.find(p=>p.id===id);if(p)return p.name}return"Player"}
const PALETTE=["#6B21A8","#B91C1C","#0F766E","#111827","#C2410C","#B45309","#1D4ED8","#15803D","#BE185D","#0369A1"];
function tmeta(id){const t=teamOf(id);if(!t)return{name:"TBD",color:"#64748B",logo:"",short:"TBD",initials:"?"};
  const nm=t.name.trim().toUpperCase();const pre=PRESET.find(p=>p.name===nm)||PRESET.find(p=>p.name.split(" ")[0]===nm.split(" ")[0]);const idx=(T.teams.indexOf(t)+10)%10;
  const words=t.name.trim().split(/\s+/);const initials=(words.length>1?words[0][0]+words[words.length-1][0]:t.name.slice(0,2)).toUpperCase();
  return{name:t.name,color:pre?.color||PALETTE[idx],logo:pre?.logo?"logos/"+pre.logo:"",sponsor:pre?.sponsor||(KIDS?KSP[nm]||"":""),short:words[0].length>=5?words[0]:words.slice(0,2).join(" "),initials}}
function badge(id,size){const m=tmeta(id);const sz=size||32;
  return m.logo?`<img class="badge" src="${esc(m.logo)}" alt="" width="${sz}" height="${sz}" style="--sz:${sz}px" onerror="this.outerHTML='<span class=badge style=\'--sz:${sz}px;background:${m.color}\'>${esc(m.initials)}</span>'">`
    :`<span class="badge" style="--sz:${sz}px;background:${m.color}">${esc(m.initials)}</span>`}
const teamLine=(id,cls,sp)=>{const s=sp&&tmeta(id).sponsor;return`<span class="tl ${cls||""}" data-act="team" data-id="${id}">${badge(id,26)}<span class="tn">${esc(tname(id))}${s?`<span class="tsp">${esc(s)}</span>`:""}</span></span>`};
function pteam(id){for(const t of T?.teams||[])if(t.players.some(p=>p.id===id))return t.id;return null}
const isLegal=b=>b.t!=="wd"&&b.t!=="nb";
const ovs=l=>Math.floor(l/6)+"."+(l%6);
const ballRuns=b=>b.t==="wd"?T.wideRuns+b.r:b.t==="nb"?T.nbRuns+b.r:b.r;
const rate=(r,l)=>l?(r*6/l).toFixed(2):"0.00";
const mOvers=m=>m.overs||T.overs;
const ovFor=(m,i)=>i===1&&m.ov2?m.ov2:mOvers(m);
function xiOf(m,team){const x=m.xi?.[team];if(x&&x.length)return x;return(teamOf(team)?.players||[]).slice(0,T.xi).map(p=>p.id)}
const maxW=(m,team)=>Math.max(1,xiOf(m,team).length-1);
const xiPlayers=(m,team)=>xiOf(m,team).map(id=>({id,name:pname(id)}));

/* special overs: powerplay 1–2 and the Mascon over (7th of 12, 6th of 10); 8 overs: 1st + Mascon */
function specials(overs){
  if(overs>=9)return{pp:[1,2],mascon:Math.floor(overs/2)+1};
  if(overs>=7)return{pp:[1],mascon:Math.floor(overs/2)+1};
  return{pp:[],mascon:null};
}
function overTag(overs,n){const s=specials(overs);if(s.pp.includes(n))return"Powerplay";if(s.mascon===n)return"Mascon over";return""}
/* bowling matrix, five bowlers minimum: 12 ov = 2×3 + 3×2, 10 ov = 5×2, 8 ov = 3×2 + 2×1 */
function matrix(overs){const max=Math.ceil(overs/5);return{max,atMax:overs-5*(max-1)}}

// Laws: off a no ball or a free hit only run out; off a wide only run out or stumped.
function allowedOuts(b){if(b.t==="nb"||b.fh)return["ro"];if(b.t==="wd")return["ro","st"];return null}
function validW(b){if(!b.w)return null;const ok=allowedOuts(b);return ok&&!ok.includes(b.w.k)?null:b.w}
function invalidW(b){return!!b.w&&!validW(b)}
const KINDS=[["b","Bowled"],["c","Caught"],["ro","Run out"],["st","Stumped"],["lbw","LBW"],["hw","Hit wicket"],["x","Other"]];
function dismissal(b){
  const bw=pname(b.bw),f=b.w.f?pname(b.w.f):"";
  switch(b.w.k){
    case"b":return"b "+bw;
    case"c":return b.w.f===b.bw?"c & b "+bw:(f?"c "+f+" ":"c ")+"b "+bw;
    case"ro":return"run out"+(f?" ("+f+")":"");
    case"st":return"st "+(f||"keeper")+" b "+bw;
    case"lbw":return"lbw b "+bw;
    case"hw":return"hit wicket b "+bw;
    default:return"out";
  }
}
function chip(b){
  let t,c="";
  if(b.t==="run"){t=b.r===0?"•":b.r;c=b.r===4?"f":b.r===6?"s":""}
  else if(b.t==="wd"){const n=ballRuns(b);t=(n>1?n:"")+"wd";c="x"}
  else if(b.t==="nb"){t="nb"+(b.r?"+"+b.r:"");c=b.r===4?"f":b.r===6?"s":"x"}
  else{t=b.r+(b.t==="bye"?"b":"lb");c="x"}
  if(validW(b)){t="W"+(b.r?"+"+b.r:"");c="w"}
  return`<span class="b ${c}">${esc(t)}</span>`;
}

/* ================= engine ================= */
function innStats(inn){
  const st={runs:0,wk:0,legal:0,ex:{wd:0,nb:0,b:0,lb:0},bat:{},batOrder:[],bowl:{},bowlOrder:[],fow:[],cur:[],log:[],overBowler:{}};
  const B=id=>{if(!id)return null;if(!st.bat[id]){st.bat[id]={r:0,b:0,f:0,s:0,out:null};st.batOrder.push(id)}return st.bat[id]};
  const W=id=>{if(!st.bowl[id]){st.bowl[id]={l:0,r:0,w:0,wd:0,nb:0};st.bowlOrder.push(id)}return st.bowl[id]};
  (inn.open||[]).forEach(B);
  let over=[];
  for(const b of inn.balls){
    B(b.s);B(b.ns);
    const bt=st.bat[b.s],bw=W(b.bw),tot=ballRuns(b),before=st.legal;
    st.overBowler[Math.floor(before/6)+1]=b.bw;
    st.runs+=tot;
    if(b.t==="run"||b.t==="nb"){bt.r+=b.r;if(b.r===4)bt.f++;if(b.r===6)bt.s++}
    if(b.t!=="wd")bt.b++;
    if(b.t==="wd"){st.ex.wd+=tot;bw.r+=tot;bw.wd++}
    else if(b.t==="nb"){st.ex.nb+=T.nbRuns;bw.r+=tot;bw.nb++}
    else if(b.t==="bye")st.ex.b+=b.r;
    else if(b.t==="lb")st.ex.lb+=b.r;
    else bw.r+=b.r;
    if(isLegal(b)){st.legal++;bw.l++}
    over.push(b);
    if(validW(b)){st.wk++;const o=B(b.w.out);o.out=dismissal(b);if(b.w.k!=="ro"&&b.w.k!=="x")bw.w++;
      st.fow.push({n:st.wk,r:st.runs,id:b.w.out,ov:ovs(st.legal)})}
    st.log.push({b,lab:Math.floor(before/6)+"."+(before%6+1)});
    if(isLegal(b)&&st.legal%6===0)over=[];
  }
  st.cur=over;
  return st;
}
function targetOf(m){if(m.inn.length<2)return null;return m.tgt||innStats(m.inn[0]).runs+1}
function isFreeHit(inn){if(!T.freeHit)return false;const l=last(inn.balls);return!!l&&(l.t==="nb"||(l.fh&&l.t==="wd"))}
function availBatters(m,inn){const st=innStats(inn);const used=new Set([...st.batOrder,inn.cur.s,inn.cur.ns].filter(Boolean));return xiPlayers(m,inn.bat).filter(p=>!used.has(p.id))}
function bowlerOptions(m,i){
  const inn=m.inn[i],st=innStats(inn),overs=ovFor(m,i),mx=matrix(overs),sp=specials(overs);
  const next=Math.floor(st.legal/6)+1;
  const prev=st.legal>0?st.overBowler[next-1]:null;
  const atMax=Object.keys(st.bowl).filter(id=>st.bowl[id].l>=mx.max*6).length;
  const isSpecial=n=>sp.pp.includes(n)||sp.mascon===n;
  const specialBy=new Set(Object.entries(st.overBowler).filter(([n])=>isSpecial(+n)&&+n!==next).map(([,id])=>id));
  return xiPlayers(m,inn.bowl).map(p=>{
    const done=Math.floor((st.bowl[p.id]?.l||0)/6);let why="",block=false;
    if(p.id===prev){why="bowled last over";block=true}
    else if(done>=mx.max)why=`${mx.max}-over quota done`;
    else if(done===mx.max-1&&mx.max>1&&atMax>=mx.atMax)why=`${mx.atMax} bowlers already bowled ${mx.max}`;
    else if(isSpecial(next)&&specialBy.has(p.id))why="already bowled a special over";
    return{id:p.id,name:`${p.name} (${done} ov)`,disabled:block,why};
  });
}
function checkEnd(m){
  const i=m.inn.length-1,inn=m.inn[i],st=innStats(inn),tg=targetOf(m);
  if(st.wk>=maxW(m,inn.bat)||st.legal>=ovFor(m,i)*6||(tg&&st.runs>=tg))closeInn(m);
}
function closeInn(m){last(m.inn).closed=true;if(m.inn.length===1)m.status="break";else finalize(m)}
function finalize(m){
  const s2=innStats(m.inn[1]),i2=m.inn[1],tg=targetOf(m);
  m.how="normal";
  if(s2.runs>=tg){const w=maxW(m,i2.bat)-s2.wk,left=ovFor(m,1)*6-s2.legal;
    m.winner=i2.bat;m.result=`${tname(i2.bat)} won by ${w} wicket${w===1?"":"s"}`+(left>0?` (${left} ball${left===1?"":"s"} left)`:"");m.status="done"}
  else if(s2.runs===tg-1){
    if(isLeague(m)){m.winner="tie";m.result="Match tied · 1 point each";m.status="done"}
    else{m.winner=null;m.result="Scores level · Super Over to decide";m.status="super"}
  }else{const d=tg-1-s2.runs;m.winner=m.inn[0].bat;m.result=`${tname(m.inn[0].bat)} won by ${d} run${d===1?"":"s"}`;m.status="done"}
}
function batFirst(m){return m.chose==="bat"?m.toss:(m.toss===m.a?m.b:m.a)}

/* ================= tables & stats ================= */
function pointsTable(group){
  const rows={};(T?.teams||[]).filter(t=>t.group===group).forEach(t=>rows[t.id]={id:t.id,p:0,w:0,l:0,t:0,nr:0,pts:0,rf:0,bf:0,ra:0,bb:0});
  Object.values(M).filter(m=>m.stage===group&&m.status==="done").forEach(m=>{
    if(m.how==="normal"&&m.inn.length===2)m.inn.forEach((inn,i)=>{const st=innStats(inn);const balls=st.wk>=maxW(m,inn.bat)?ovFor(m,i)*6:st.legal;
      const R=rows[inn.bat],F=rows[inn.bowl];if(R){R.rf+=st.runs;R.bf+=balls}if(F){F.ra+=st.runs;F.bb+=balls}});
    [m.a,m.b].forEach(id=>{const r=rows[id];if(!r)return;r.p++;
      if(m.winner==="tie"){r.t++;r.pts+=T.ptsTie}else if(m.winner==="nr"){r.nr++;r.pts+=T.ptsNR}else if(m.winner===id){r.w++;r.pts+=T.ptsWin}else r.l++});
  });
  return Object.values(rows).map(r=>({...r,nrr:(r.bf?r.rf/(r.bf/6):0)-(r.bb?r.ra/(r.bb/6):0)})).sort((a,b)=>b.pts-a.pts||b.nrr-a.nrr||b.w-a.w);
}
function tourStats(){
  const bat={},bowl={};
  Object.values(M).forEach(m=>(m.inn||[]).forEach(inn=>{const st=innStats(inn);
    st.batOrder.forEach(id=>{const b=st.bat[id],x=bat[id]||(bat[id]={r:0,b:0,f:0,s:0,inns:0,outs:0,hs:-1,hsNo:false});
      x.r+=b.r;x.b+=b.b;x.f+=b.f;x.s+=b.s;x.inns++;if(b.out)x.outs++;if(b.r>x.hs||(b.r===x.hs&&!b.out)){x.hs=b.r;x.hsNo=!b.out}});
    st.bowlOrder.forEach(id=>{const b=st.bowl[id],x=bowl[id]||(bowl[id]={l:0,r:0,w:0,bw:-1,br:0});
      x.l+=b.l;x.r+=b.r;x.w+=b.w;if(b.w>x.bw||(b.w===x.bw&&b.r<x.br)){x.bw=b.w;x.br=b.r}});
  }));
  return{bat,bowl};
}



/* ================= milestones ================= */
const MS_BAT=[30,50,75],MS_WK=[3,5],MS_TEAM=[50,100,150];
function milestones(m){
  const out=[];
  (m.inn||[]).forEach((inn,ii)=>{
    const br={},bw={},seq={};let runs=0,legal=0,ovRuns=0,ovSix=0,ovBalls=[],part=0,partKey="";const hit=new Set();
    const push=(idx,type,text,pid)=>out.push({key:`${m.id}:${ii}:${idx}:${type}:${pid||""}`,ii,idx,type,text,pid});
    inn.balls.forEach((b,idx)=>{
      const tot=ballRuns(b);runs+=tot;const w=validW(b);
      // batter
      if(b.t==="run"||b.t==="nb"){const before=br[b.s]||0;br[b.s]=before+b.r;MS_BAT.forEach(t=>{if(before<t&&br[b.s]>=t)push(idx,"bat",`${t} for ${pname(b.s)}`,b.s)})}
      // partnership
      const pk=[b.s,b.ns].sort().join("|");if(pk!==partKey){partKey=pk;part=0;hit.delete("part")}
      part+=tot;if(part>=50&&!hit.has("part")){hit.add("part");push(idx,"part",`50 partnership: ${pname(b.s)} & ${pname(b.ns)}`)}
      if(w)part=0,hit.delete("part"),partKey="";
      // team
      MS_TEAM.forEach(t=>{if(runs-tot<t&&runs>=t)push(idx,"team",`${tname(inn.bat)} ${t} up`)});
      // bowler wickets + hat-trick
      if(w&&w.k!=="ro"&&w.k!=="x"){const before=bw[b.bw]||0;bw[b.bw]=before+1;MS_WK.forEach(t=>{if(before<t&&bw[b.bw]>=t)push(idx,"wkt",`${t} wickets for ${pname(b.bw)}`,b.bw)})}
      if(b.t!=="wd"&&b.t!=="nb"){const s=seq[b.bw]||(seq[b.bw]=[]);s.push(!!(w&&w.k!=="ro"&&w.k!=="x"));if(s.length>=3&&s.slice(-3).every(Boolean)&&!(s.length>=4&&s.slice(-4).every(Boolean)))push(idx,"hat",`Hat-trick for ${pname(b.bw)}!`,b.bw)}
      // over
      ovRuns+=tot;if((b.t==="run"||b.t==="nb")&&b.r===6)ovSix++;ovBalls.push(b);
      if(isLegal(b)){legal++;if(legal%6===0){
        const bowlerRuns=ovBalls.reduce((x,y)=>x+(y.t==="bye"||y.t==="lb"?0:ballRuns(y)),0);
        if(bowlerRuns===0&&ovBalls.every(y=>isLegal(y)))push(idx,"maiden",`Maiden over by ${pname(b.bw)}`,b.bw);
        if(ovRuns>=20)push(idx,"over",`${ovRuns} runs off the over from ${pname(b.bw)}`);
        else if(ovSix>=3)push(idx,"over",`${ovSix} sixes in the over`);
        ovRuns=0;ovSix=0;ovBalls=[]}}
    });
  });
  return out;
}
const MS_ICON={bat:"🏏",part:"🤝",team:"📈",wkt:"🎯",hat:"🎩",maiden:"🧱",over:"💥"};
let msSeen=null;
function msToast(list){
  list.slice(-3).forEach((x,i)=>setTimeout(()=>{
    const el=document.createElement("div");el.className="mstoast";el.innerHTML=`<span class="mi">${MS_ICON[x.type]||"⭐"}</span><span><small>${esc(stageLabel(M[x.key.split(":")[0]]||{}))}</small><b>${esc(x.text)}</b></span>`;
    el.addEventListener("click",()=>{ui.sel=x.key.split(":")[0];ui.tab="live";render();el.remove()});
    document.body.appendChild(el);requestAnimationFrame(()=>el.classList.add("in"));
    setTimeout(()=>{el.classList.remove("in");setTimeout(()=>el.remove(),400)},6000);
  },i*1800));
}
function msCheck(){
  const live=Object.values(M).filter(m=>m.status==="live"||m.status==="break"||m.status==="done");
  const all=live.flatMap(milestones);const keys=new Set(all.map(x=>x.key));
  if(msSeen===null){msSeen=keys;return}
  const fresh=all.filter(x=>!msSeen.has(x.key)&&M[x.key.split(":")[0]]&&(Date.now()-(M[x.key.split(":")[0]].upd||0))<10*60*1000);
  msSeen=keys;if(fresh.length&&!canScore)msToast(fresh);else if(fresh.length&&canScore)msToast(fresh.slice(-1));
}

/* ================= fantasy ================= */
const FP={run:1,four:1,six:2,thirty:4,fifty:8,wkt:25,haul3:8,field:8,dot:1,maiden:12,duck:-2};
function matchPoints(m){
  const pts={};const add=(id,n)=>{if(id)pts[id]=(pts[id]||0)+n};
  (m.inn||[]).forEach(inn=>{
    const st=innStats(inn);
    st.batOrder.forEach(id=>{const b=st.bat[id];let p=b.r*FP.run+b.f*FP.four+b.s*FP.six;if(b.r>=50)p+=FP.fifty;else if(b.r>=30)p+=FP.thirty;if(b.out&&b.r===0&&b.b>0)p+=FP.duck;add(id,p)});
    st.bowlOrder.forEach(id=>{const b=st.bowl[id];add(id,b.w*FP.wkt+(b.w>=3?FP.haul3:0))});
    inn.balls.forEach(b=>{
      if(validW(b)){if(b.w.k==="c"||b.w.k==="st")add(b.w.f,FP.field);if(b.w.k==="ro"&&b.w.f)add(b.w.f,FP.field)}
      if(b.t==="run"&&b.r===0&&!b.w)add(b.bw,FP.dot);
    });
    // maiden: six legal balls, no runs off bat or extras charged to the bowler
    let ov=[],clean=true;
    inn.balls.forEach(b=>{if(!isLegal(b))clean=false;else{if(b.r>0&&b.t!=="bye")clean=false;ov.push(b);if(ov.length===6){if(clean)add(ov[0].bw,FP.maiden);ov=[];clean=true}}});
  });
  return pts;
}
function fantasyPoints(doneOnly){
  const pts={};Object.values(M).forEach(m=>{if(doneOnly&&m.status!=="done")return;const mp=matchPoints(m);for(const k in mp)pts[k]=(pts[k]||0)+mp[k]});return pts;
}
function mvpTable(filter){
  const pts=fantasyPoints();const{bat,bowl}=tourStats();const field={},mt={};
  Object.values(M).forEach(m=>(m.inn||[]).forEach(inn=>{const seen=new Set();inn.balls.forEach(b=>{[b.s,b.ns,b.bw].forEach(id=>{if(id&&!seen.has(id)){seen.add(id);mt[id]=(mt[id]||new Set());mt[id].add(m.id)}});
    if(validW(b)&&b.w.f&&(b.w.k==="c"||b.w.k==="st"||b.w.k==="ro")){field[b.w.f]=(field[b.w.f]||0)+1;mt[b.w.f]=(mt[b.w.f]||new Set());mt[b.w.f].add(m.id)}})}));
  return Object.keys(pts).filter(id=>pteam(id)&&(!filter||filter(id))).map(id=>({id,pts:pts[id],r:bat[id]?.r||0,w:bowl[id]?.w||0,f:field[id]||0,m:mt[id]?.size||0})).sort((a,b)=>b.pts-a.pts||b.r-a.r);
}
function matchMvp(m){
  if(!m.inn||!m.inn.length)return null;const top=Object.entries(matchPoints(m)).filter(([id])=>pteam(id)).sort((a,b)=>b[1]-a[1])[0];return top?{id:top[0],pts:top[1]}:null;
}
function fantasyLocked(){return Object.values(M).some(m=>(m.inn||[]).some(i=>i.balls.length>0))}
async function loadFantasy(force){
  if(!db)return;const now=Date.now();if(!force&&FT.all&&now-FT.allAt<120000)return;FT.allAt=now;
  // Leaderboard comes from ONE saved record (meta/board) that the scorer's phone updates after every match.
  // Fans never read the whole fantasy collection: 1 read for the board + 1 for their own team.
  try{const b=await getBoard(force);FT.all=(b&&b.f)||[];if(b&&b.subs&&!canScore)SUBS=b.subs;
    if(FT.myId&&(force||!FT.mine)){const d=await getDoc(doc(db,C("fantasy"),FT.myId));FT.mine=d.exists()?{id:d.id,...d.data()}:null}
    scheduleRender()}catch(e){}
}
/* ===== Fantasy rules: 13 players, min 3 bat/WK, 2 bowl, 3 AR, max 3 per team, max 2 icons, C 2x / VC 1.5x,
   2 substitutions in each of 2 windows (before match day 2 and 3). Entry fields: p,c,vc (match day 1), p1,c1,vc1, p2,c2,vc2. ===== */
const FR={n:13,minBat:3,minBowl:2,minAr:3,maxTeam:3,maxIcon:2,maxSubs:2};
let SUBS={phase:0,open:false};
const ICONS=new Set((window.MASCON_TEAMS||[]).map(t=>String(t.icon||"").trim().toLowerCase()).filter(Boolean));
let _pm=null,_pmT=null;
function pinfo(id){if(_pmT!==T){_pmT=T;_pm={};allPlayers().forEach(p=>_pm[p.id]=p)}return _pm[id]}
function isIcon(id){const p=pinfo(id);return!!p&&ICONS.has(p.name.trim().toLowerCase())}
function rgroup(id){const r=String(pinfo(id)?.role||"").toUpperCase();return r==="BOWL"?"bowl":r==="AR"?"ar":"bat"}
function tcount(p){const c={bat:0,bowl:0,ar:0,icons:0,teams:{}};p.forEach(id=>{c[rgroup(id)]++;if(isIcon(id))c.icons++;const t=pinfo(id)?.tid;c.teams[t]=(c.teams[t]||0)+1});return c}
function needOf(c){return Math.max(0,FR.minBat-c.bat)+Math.max(0,FR.minBowl-c.bowl)+Math.max(0,FR.minAr-c.ar)}
function needText(c){const a=[];if(c.bat<FR.minBat)a.push(`${FR.minBat-c.bat} more batter/WK`);if(c.bowl<FR.minBowl)a.push(`${FR.minBowl-c.bowl} more bowler${FR.minBowl-c.bowl>1?"s":""}`);if(c.ar<FR.minAr)a.push(`${FR.minAr-c.ar} more all-rounder${FR.minAr-c.ar>1?"s":""}`);return a.join(", ")}
// Why this player can't be added right now ("" = OK)
function cantAdd(p,id,base){
  if(p.includes(id))return"";
  if(p.length>=FR.n)return"Your team already has 13 players. Remove one first.";
  const c=tcount(p),t=pinfo(id)?.tid;
  if((c.teams[t]||0)>=FR.maxTeam)return`At most ${FR.maxTeam} players from one team.`;
  if(isIcon(id)&&c.icons>=FR.maxIcon)return`At most ${FR.maxIcon} icon players.`;
  const g=rgroup(id),helps=(g==="bat"&&c.bat<FR.minBat)||(g==="bowl"&&c.bowl<FR.minBowl)||(g==="ar"&&c.ar<FR.minAr);
  if(!helps&&FR.n-p.length-1<needOf(c))return`Fill the minimums first: you still need ${needText(c)}.`;
  if(base&&!base.includes(id)&&p.filter(x=>!base.includes(x)).length>=FR.maxSubs)return`Only ${FR.maxSubs} substitutions in this window. Put a player back to swap someone else.`;
  return"";
}
function teamProblems(d){
  const p=d.p,c=tcount(p),out=[];
  if(p.length!==FR.n)out.push(`Pick ${FR.n} players (${p.length} so far).`);
  if(needOf(c))out.push(`You still need ${needText(c)}.`);
  if(Object.values(c.teams).some(n=>n>FR.maxTeam))out.push(`At most ${FR.maxTeam} players from one team.`);
  if(c.icons>FR.maxIcon)out.push(`At most ${FR.maxIcon} icon players.`);
  if(!d.c||!p.includes(d.c))out.push("Choose your captain.");
  if(!d.vc||!p.includes(d.vc))out.push("Choose your vice-captain.");
  if(d.c&&d.c===d.vc)out.push("Captain and vice-captain must be different players.");
  if(d.base&&p.filter(x=>!d.base.includes(x)).length>FR.maxSubs)out.push(`Only ${FR.maxSubs} substitutions in this window.`);
  return out;
}
// Which saved version of a team applies in phase ph (0 = match day 1, 1 = after window 1, 2 = after window 2)
function verAt(t,ph){for(let k=Math.min(ph,2);k>=1;k--)if(t["p"+k])return{p:t["p"+k],c:t["c"+k],vc:t["vc"+k]};return{p:t.p||[],c:t.c,vc:t.vc}}
function fantasyPer(){const per=[];Object.values(M).forEach(m=>{if(m.status==="done")per.push([m.ph||0,matchPoints(m)])});return per}
function teamPts(t,per){let s=0;per.forEach(([ph,mp])=>{const v=verAt(t,ph);(v.p||[]).forEach(id=>{const x=mp[id]||0;s+=id===v.c?x*2:id===v.vc?x*1.5:x})});return Math.round(s*10)/10}
function fantasyBoard(){
  const per=fantasyPer();
  return (FT.all||[]).map(t=>({...t,pts:teamPts(t,per)})).sort((a,b)=>b.pts-a.pts||a.name.localeCompare(b.name));
}
function allPlayers(){return(T?.teams||[]).flatMap(t=>t.players.map(p=>({id:p.id,name:p.name,role:p.role||"",age:p.age||null,team:t.name,tid:t.id})))}
function pAge(id){for(const t of T?.teams||[]){const p=t.players.find(p=>p.id===id);if(p)return p.age||null}return null}
async function loadFans(force){
  if(!db)return;const now=Date.now();if(!force&&FAN.all&&now-FAN.at<120000)return;FAN.at=now;
  try{const b=await getBoard(force);FAN.all=(b&&b.fans)||{};FAN.polls=(b&&b.polls)||{};scheduleRender()}catch(e){}
}
let BOARD=null,boardAt=0,boardP=null;
async function getBoard(force){
  const now=Date.now();if(!force&&BOARD&&now-boardAt<120000)return BOARD;
  if(boardP)return boardP;
  boardP=getDoc(doc(db,C("meta"),"board")).then(d=>{BOARD=d.exists()?d.data():null;boardAt=Date.now();boardP=null;return BOARD}).catch(e=>{boardP=null;return BOARD});
  return boardP;
}
// Scorer only: rebuild the leaderboards record from all entries. Runs when a match finishes, at the first ball, or from Setup.
const boardSig={};let boardBusy=false,boardAgain=false;
async function publishBoard(manual){
  if(!db||!canScore)return;if(boardBusy){boardAgain=true;return}boardBusy=true;
  try{const locked=fantasyLocked();
    const [fs,fn,pl]=await Promise.all([getDocs(collection(db,C("fantasy"))),getDocs(collection(db,C("fans"))),getDocs(collection(db,C("polls")))]);
    const KEEP=["p","c","vc","p1","c1","vc1","p2","c2","vc2"];
    const f=fs.docs.filter(d=>!d.data().demo).map(d=>{const x=d.data(),o={id:d.id,name:x.name||"Fan"};if(locked)KEEP.forEach(k=>{if(x[k]!==undefined)o[k]=x[k]});return o});
    const fans={};fn.docs.forEach(d=>fans[d.id]=d.data().name||"Fan");
    const polls={};pl.docs.forEach(d=>polls[d.id]=d.data());
    await setDoc(doc(db,C("meta"),"board"),{f,fans,polls,subs:SUBS,at:Date.now()});
    BOARD={f,fans,polls,subs:SUBS};boardAt=Date.now();FT.all=f;FAN.all=fans;FAN.polls=polls;
    if(manual)flash(`Leaderboards updated: ${f.length} fantasy teams, ${Object.keys(fans).length} prediction fans.`,true);
  }catch(e){if(manual)flash("Leaderboards not updated. Check your connection.")}
  boardBusy=false;if(boardAgain){boardAgain=false;publishBoard()}
}
function dayKey(m){return m&&m.when?String(m.when).slice(0,10):null}
async function setSubs(n){SUBS={phase:n.phase,open:n.open};if(DEMO||!db)return;try{await setDoc(doc(db,C("meta"),"subs"),{...SUBS,at:Date.now()})}catch(e){}}
async function loadSubs(){if(!db||KIDS)return;try{const d=await getDoc(doc(db,C("meta"),"subs"));if(d.exists()){const x=d.data();SUBS={phase:x.phase||0,open:!!x.open}}}catch(e){}}
// After a match ends: if every match on that date is done and a later match day exists, open the next substitution window.
async function maybeOpenSubs(m){
  if(KIDS||SUBS.open||SUBS.phase>=2)return;const d=dayKey(m);if(!d)return;
  const all=Object.values(M);if(!all.filter(x=>dayKey(x)===d).every(x=>x.status==="done"))return;
  if(!all.some(x=>dayKey(x)&&dayKey(x)>d&&x.status!=="done"))return;
  await setSubs({phase:SUBS.phase+1,open:true});
}
function maybePublishBoard(m){
  if(!canScore||KIDS)return;
  // First ball of a match: voting has just closed, so save that match's predictions now (nothing left to do at the end).
  const started=(m.inn||[]).some(i=>i.balls.length);
  if(started&&!boardSig[m.id+":start"]){boardSig[m.id+":start"]=1;setTimeout(async()=>{if(SUBS.open)await setSubs({phase:SUBS.phase,open:false});publishBoard()},1500)}
  // Match ended: save again straight away so every table is current. No confirm step for the scorer.
  if(m.status==="done"){const sig=m.result||"done";if(boardSig[m.id]!==sig){boardSig[m.id]=sig;setTimeout(async()=>{await maybeOpenSubs(m);publishBoard()},500)}}
  else if(boardSig[m.id])delete boardSig[m.id];
}
function predictionBoard(){
  if(!FAN.polls)return[];const score={},tot={};
  Object.entries(FAN.polls).forEach(([mid,picks])=>{const m=M[mid];if(!m||m.status!=="done"||!m.winner||m.winner==="tie"||m.winner==="nr")return;
    Object.entries(picks).forEach(([u,team])=>{tot[u]=(tot[u]||0)+1;if(team===m.winner)score[u]=(score[u]||0)+1})});
  return Object.keys(tot).map(u=>({u,name:(FAN.all&&FAN.all[u])||"Fan",c:score[u]||0,n:tot[u]})).sort((a,b)=>b.c-a.c||a.n-b.n||a.name.localeCompare(b.name));
}
function predictionHtml(){
  loadFans();const rows=predictionBoard();const decided=Object.values(M).filter(m=>m.status==="done"&&m.winner&&m.winner!=="tie"&&m.winner!=="nr").length;
  if(!rows.length)return`<h2>Prediction league</h2><p class="kv">Predict the winner of each match before the toss. One point per correct call. The table appears after the first result.</p>`;
  const medal=i=>i===0?"🥇":i===1?"🥈":i===2?"🥉":i+1;
  return`<h2>Prediction league</h2><p class="kv">One point per correct winner. ${decided} match${decided===1?"":"es"} decided.</p><div class="tbl"><table><thead><tr><th>#</th><th style="text-align:left">Fan</th><th>Correct</th><th>Calls</th></tr></thead><tbody>${rows.slice(0,50).map((r,i)=>`<tr${r.u===uid?' class="q"':""}><td style="text-align:left">${medal(i)}</td><td class="n" style="text-align:left"><b>${esc(r.name)}</b>${r.u===uid?'<span class="tag">YOU</span>':""}</td><td><b>${r.c}</b></td><td>${r.n}</td></tr>`).join("")}</tbody></table></div>`;
}
function fantasyView(){
  if(!T||!T.teams.length||!T.teams.every(t=>t.players.length>=DEF.minXi))return`<section><div class="empty"><strong>Fantasy league opens after the auction</strong>Once the squads are in, pick your 13 players. Read the rules below before you build your team.</div>${iosNoteHtml()}${fantasyRulesHtml(true)}${T?predictionHtml():""}</section>`;
  loadFantasy();
  const locked=fantasyLocked(),pts=fantasyPoints(true);
  const board=fantasyBoard();
  const rank=FT.mine?board.findIndex(t=>t.id===FT.mine.id)+1:0;
  const nm=id=>{const p=allPlayers().find(p=>p.id===id);return p?`<span class="tl">${badge(p.tid,22)}<span class="tn">${esc(p.name)} <span class="muted small">${esc(p.role)}</span></span></span>`:"Player"};
  let mine="";
  if(FT.draft&&!locked)mine=pickerHtml();
  else if(FT.draft&&FT.draft.mode==="sub"&&SUBS.open)mine=pickerHtml();
  else if(FT.mine){
    const my=board.find(t=>t.id===FT.mine.id)||{...FT.mine,pts:teamPts(FT.mine,fantasyPer())};
    const v=verAt(FT.mine,SUBS.phase),cv=id=>id===v.c?'<span class="cvt">C</span>':id===v.vc?'<span class="cvt vc">VC</span>':"";
    const used=SUBS.phase>=1&&FT.mine["p"+SUBS.phase]?(FT.mine["p"+SUBS.phase]).filter(x=>!verAt(FT.mine,SUBS.phase-1).p.includes(x)).length:0;
    const foot=!locked?`<div class="row-btns"><button class="btn" data-act="fEdit">Change my team</button><button class="btn warn" data-act="fForget">Not my team</button></div>`
      :SUBS.open?`<div class="subwin"><b>Substitution window open</b> for match day ${SUBS.phase+1}: up to ${FR.maxSubs} changes${used?` (${used} used)`:""}, and you can change your captain and vice-captain. Closes at the first ball.</div><div class="row-btns"><button class="btn pri" data-act="fSub">Make substitutions</button></div>`
      :`<p class="kv">Team locked.${SUBS.phase<2?` Substitutions open after match day ${SUBS.phase+1} ends.`:" No more substitutions."}</p>`;
    mine=`<div class="panel"><div class="row-btns" style="justify-content:space-between;align-items:center"><h2>${esc(my.name)}'s XIII</h2><span class="bigpts">${my.pts||0} pts${rank?` · #${rank}`:""}</span></div>
    <div class="tbl"><table><thead><tr><th>Player</th><th>Pts</th></tr></thead><tbody>${(v.p||[]).map(id=>`<tr><td class="n">${nm(id)}${cv(id)}</td><td><b>${pts[id]||0}</b></td></tr>`).join("")}</tbody></table></div>
    <p class="kv small">Player points are his tournament total. Your score counts captain 2×, vice-captain 1.5×, and only the matches he played for you.</p>${foot}</div>`;
  }else mine=locked?`<div class="panel"><h2>Entries closed</h2><p class="kv">Fantasy teams locked when the first ball was bowled.</p></div>`
    :`<div class="panel"><h2>Build your XIII</h2><p class="kv">Pick any 13 players from the 10 squads. One team per person; it locks at the first ball on 29 November.</p><button class="btn pri" data-act="fNew">Pick my 13</button></div>`;
  const medal=i=>i===0?"🥇":i===1?"🥈":i===2?"🥉":i+1;
  const picksPanel=t=>{const v=verAt(t,SUBS.phase);return`<div class="pickpanel"><div class="label">${esc(t.name)} · 13 players${v.c?` · C ${esc(pname(v.c))} · VC ${esc(pname(v.vc))}`:""}</div><div class="pickgrid">${(v.p||[]).map(id=>({id,p:pts[id]||0})).sort((a,b)=>b.p-a.p).map(x=>`<span class="pk" data-act="player" data-id="${x.id}">${badge(pteam(x.id),20)}<span>${esc(pname(x.id))}</span><b>${x.p}</b></span>`).join("")}</div></div>`};
  const openT=locked&&ui.fopen?board.find(t=>t.id===ui.fopen):null;
  const lb=board.length?`<h2>Leaderboard</h2>${locked?`<p class="kv">Updated after every match. Tap a top-10 team to see its 13 players.</p>`:`<p class="kv">Picks are hidden until entries lock at the first ball.</p>`}${openT?picksPanel(openT):""}<div class="tbl"><table><thead><tr><th>#</th><th style="text-align:left">Team</th><th>Pts</th></tr></thead><tbody>${board.slice(0,100).map((t,i)=>`<tr class="${t.id===FT.mine?.id?"q ":""}${locked&&i<10?"exp":""}${ui.fopen===t.id?" sel":""}"${locked&&i<10?` data-act="fopen" data-id="${t.id}"`:""}><td style="text-align:left">${medal(i)}</td><td class="n" style="text-align:left"><b>${esc(t.name)}</b>${t.id===FT.mine?.id?'<span class="tag">YOU</span>':""}${locked&&i<10?`<span class="caret">${ui.fopen===t.id?"▾":"▸"}</span>`:""}</td><td><b>${t.pts}</b></td></tr>`).join("")}</tbody></table></div><p class="kv">${board.length} team${board.length===1?"":"s"} entered.</p>`:"";
  const scoring=`<details class="card"><summary><span>How points work</span></summary><div class="in kv">Run 1 · Four +1 · Six +2 · 30 runs +4 · 50 runs +8 · Duck −2<br>Wicket 25 · 3 wickets +8 · Catch, stumping or run-out 8<br>Dot ball 1 · Maiden over 12<br>Captain 2× · Vice-captain 1.5×</div></details>`;
  // Most-picked players across all entries (from the same saved board: no extra reads). Picks are only public once entries lock.
  let mp="";
  if(locked&&board.length){const cnt={};board.forEach(t=>(verAt(t,SUBS.phase).p||[]).forEach(id=>cnt[id]=(cnt[id]||0)+1));
    const top=Object.entries(cnt).filter(([id])=>pteam(id)).sort((a,b)=>b[1]-a[1]||(pts[b[0]]||0)-(pts[a[0]]||0)).slice(0,10);
    if(top.length)mp=`<h2>Most picked players</h2><p class="kv">Top 10 across all ${board.length} fantasy team${board.length===1?"":"s"}.</p><div class="tbl"><table><thead><tr><th>#</th><th style="text-align:left">Player</th><th>Picked by</th><th>Pts</th></tr></thead><tbody>${top.map(([id,c],i)=>`<tr data-act="player" data-id="${id}"><td>${medal(i)}</td><td class="n">${nm(id)}</td><td><b>${c}</b> <span class="muted small">${Math.round(c*100/board.length)}%</span></td><td>${pts[id]||0}</td></tr>`).join("")}</tbody></table></div>`;
  }else if(!locked)mp=`<h2>Most picked players</h2><p class="kv">Shows the 10 players picked by the most fantasy teams, once entries lock at the first ball.</p>`;
  const demoP=DEMO?`<div class="panel"><h2>Demo controls</h2><p class="kv">${DEMO_DAY===0?"Pick your team (the rules are checked as you pick), then play match day 1 with fake scores."
    :DEMO_DAY<3?`Match day ${DEMO_DAY} of 3 played. The substitution window is open: tap <b>Make substitutions</b> in your team to swap up to 2 players and change captain/vice-captain, then play match day ${DEMO_DAY+1}.`
    :"All 3 match days played. Final points and leaderboard below."}</p><div class="row-btns">${DEMO_DAY<3?`<button class="btn pri" data-act="demoSim">Play match day ${DEMO_DAY+1}</button>`:""}<button class="btn" data-act="demoExit">Exit demo</button></div></div>`:"";
  return`<section>${demoP}${DEMO?"":iosNoteHtml()}${fantasyRulesHtml(!FT.mine&&!locked)}${mine}${lb}${mp}${cupHtml()}${scoring}${DEMO?"":predictionHtml()}</section>`;
}
// Who a team plays next: its fixtures on the next match day (by date), or its next 2 fixtures if dates aren't set
function nextOpps(tid){
  const up=Object.values(M).filter(m=>m.status!=="done"&&(m.a===tid||m.b===tid)&&m.a&&m.b).sort((x,y)=>String(x.when||"9").localeCompare(String(y.when||"9"))||(x.no||0)-(y.no||0));
  if(!up.length)return[];const d=dayKey(up[0]);
  return(d?up.filter(m=>dayKey(m)===d):up.slice(0,2)).map(m=>m.a===tid?m.b:m.a);
}
function pickerHtml(){
  const d=FT.draft,q=FT.q.trim().toLowerCase(),sub=d.mode==="sub";
  const sel=new Set(d.p),c=tcount(d.p);
  const list=allPlayers().filter(p=>!q||p.name.toLowerCase().includes(q)||p.team.toLowerCase().includes(q));
  const byTeam={};list.forEach(p=>(byTeam[p.team]||(byTeam[p.team]=[])).push(p));
  const ins=sub?d.p.filter(x=>!d.base.includes(x)):[],outs=sub?d.base.filter(x=>!d.p.includes(x)):[];
  const ok=(b,t)=>`<li class="${b?"ok":"no"}">${b?"✓":"•"} ${t}</li>`;
  const maxT=Math.max(0,...Object.values(c.teams));
  const checks=`<ul class="fchk">${ok(d.p.length===FR.n,`13 players (${d.p.length})`)}${ok(c.bat>=FR.minBat,`At least 3 batters/WK (${c.bat})`)}${ok(c.bowl>=FR.minBowl,`At least 2 bowlers (${c.bowl})`)}${ok(c.ar>=FR.minAr,`At least 3 all-rounders (${c.ar})`)}${ok(maxT<=FR.maxTeam,`Max 3 from one team`)}${ok(c.icons<=FR.maxIcon,`Max 2 icon players (${c.icons})`)}${ok(d.c&&d.vc&&d.c!==d.vc&&sel.has(d.c)&&sel.has(d.vc),"Captain and vice-captain chosen")}${sub?ok(ins.length<=FR.maxSubs,`Substitutions used: ${ins.length} of ${FR.maxSubs}`):""}</ul>`;
  const opt=cur=>`<option value="">Choose…</option>`+d.p.map(id=>`<option value="${id}"${id===cur?" selected":""}>${esc(pname(id))}</option>`).join("");
  const probs=teamProblems(d);
  const tag=id=>`${isIcon(id)?' <span class="muted small">★ icon</span>':""}`;
  return`<div class="panel"><div class="row-btns" style="justify-content:space-between;align-items:center"><h2>${sub?`Substitutions · match day ${d.k+1}`:"Pick your 13"}</h2><span class="bigpts">${d.p.length}/13</span></div>
  ${sub?`<p class="kv">Swap up to ${FR.maxSubs} players: untick a player to take him out, tick a new one to bring him in. Points already earned stay with your team.</p>${outs.length||ins.length?`<p class="kv">${outs.map(x=>`<span class="tagout">OUT ${esc(pname(x))}</span>`).join(" ")} ${ins.map(x=>`<span class="tagin">IN ${esc(pname(x))}</span>`).join(" ")}</p>`:""}`
    :`<div class="field"><label class="label" for="f-name">Your name (shown on the leaderboard)</label><input id="f-name" value="${esc(d.name)}" maxlength="30" placeholder="e.g. Rahul D" data-fname="1"></div>`}
  ${checks}
  ${d.p.length?`<div class="chips">${d.p.map(id=>`<button class="chip" data-act="fTog" data-id="${id}">${esc(pname(id))}${id===d.c?" (C)":id===d.vc?" (VC)":""} ✕</button>`).join("")}</div>`:""}
  ${d.p.length?`<div class="grid2"><div class="field"><label class="label" for="f-c">Captain (2× points)</label><select id="f-c" data-fcap="c">${opt(d.c)}</select></div><div class="field"><label class="label" for="f-vc">Vice-captain (1.5×)</label><select id="f-vc" data-fcap="vc">${opt(d.vc)}</select></div></div>`:""}
  <input id="f-q" placeholder="Search player or team" value="${esc(FT.q)}" data-fq="1">
  ${Object.entries(byTeam).map(([team,ps])=>`<div class="label tl">${badge(ps[0].tid,20)}<span>${esc(team)}</span>${c.teams[ps[0].tid]?` <span class="muted small">${c.teams[ps[0].tid]}/3 picked</span>`:""}</div>${(o=>o.length?`<div class="fvs">Next: ${o.map(x=>`vs <b>${esc(tname(x))}</b>`).join(" · ")}</div>`:"")(nextOpps(ps[0].tid))}<div class="xi">${ps.map(p=>{const on=sel.has(p.id),why=on?"":cantAdd(d.p,p.id,sub?d.base:null);return`<label class="${on?"on":""}${why?" dim":""}"><input type="checkbox" data-fpick="${p.id}"${on?" checked":""}>${esc(p.name)}${p.role?` <span class="muted small">${esc(p.role)}</span>`:""}${tag(p.id)}</label>`}).join("")}</div>`).join("")}
  ${FT.err?`<div class="msg" style="color:var(--out)">${esc(FT.err)}</div>`:""}
  <div class="row-btns"><button class="btn pri" data-act="fSave"${probs.length?" disabled":""}>${sub?"Save substitutions":"Save my team"}</button><button class="btn" data-act="fCancel">Cancel</button></div>
  ${probs.length&&d.p.length===FR.n?`<p class="kv small">${esc(probs[0])}</p>`:""}</div>`;
}
async function saveFantasy(){
  const d=FT.draft;const probs=teamProblems(d);
  if(probs.length){FT.err=probs[0];render();return}
  if(d.mode==="sub"){
    if(!SUBS.open||SUBS.phase!==d.k){FT.err="The substitution window has closed.";render();return}
    const k=d.k,upd={["p"+k]:d.p,["c"+k]:d.c,["vc"+k]:d.vc};
    if(DEMO){Object.assign(FT.mine,upd);FT.all=[...(FT.all||[]).filter(t=>t.id!==FT.mine.id),FT.mine];FT.draft=null;FT.err="";render();flash("Substitutions saved (demo).",true);return}
    try{await setDoc(doc(db,C("fantasy"),FT.mine.id),{...upd,at:Date.now()},{merge:true});Object.assign(FT.mine,upd);FT.draft=null;FT.err="";render();flash("Substitutions saved.",true)}
    catch(e){FT.err=e?.code==="permission-denied"?"Not allowed: the window may have closed, or more than 2 players changed.":"Not saved. Check your connection.";render()}
    return;
  }
  const name=(d.name||"").trim();
  if(name.length<2){FT.err="Enter your name.";render();return}
  if(fantasyLocked()){FT.err="Entries closed: the tournament has started.";render();return}
  if(DEMO){FT.mine={id:"demo-me",name,p:d.p,c:d.c,vc:d.vc};FT.myId="demo-me";FT.all=[...(FT.all||[]).filter(t=>t.id!=="demo-me"),FT.mine];FT.draft=null;FT.err="";render();flash("Saved on this phone only (demo).",true);return}
  if(!uid){FT.err="No connection. Try again in a moment.";render();return}
  const id=uid;
  try{await setDoc(doc(db,C("fantasy"),id),{name,p:d.p,c:d.c,vc:d.vc,uid,at:Date.now()});FT.myId=id;try{localStorage.setItem(SK("mc-fid"),id)}catch(e){}
    FT.mine={id,name,p:d.p,c:d.c,vc:d.vc};FT.draft=null;FT.err="";loadFantasy(true);render()}
  catch(e){FT.err=e?.code==="permission-denied"?"Entries are closed or this name is already taken on another phone.":"Not saved. Check your connection.";render()}
}

/* ================= predictions ================= */
async function loadPoll(mid,force){
  if(!db)return;const p=polls[mid];
  // Voting closes at the first ball: after one read past that point the counts can't change, so never read again.
  const mm=M[mid],started=!!(mm&&(mm.inn||[]).some(i=>i.balls.length));
  if(!force&&p&&(p.final||Date.now()-p.at<180000))return;
  polls[mid]={c:p?.c||{},mine:p?.mine||null,at:Date.now(),final:false};
  try{const s=await getDoc(doc(db,C("polls"),mid));const d=s.exists()?s.data():{};const c={};
    for(const k in d)c[d[k]]=(c[d[k]]||0)+1;
    polls[mid]={c,mine:uid?d[uid]||null:null,at:Date.now(),final:started};scheduleRender()}catch(e){}
}
function pollHtml(m){
  if(KIDS)return"";
  if(!db)return"";const p=polls[m.id];if(!p){loadPoll(m.id);return""}
  loadPoll(m.id);
  const ca=p.c[m.a]||0,cb=p.c[m.b]||0,tot=ca+cb,pa=tot?Math.round(ca*100/tot):50;
  const open=m.status==="scheduled"||m.status==="setup";
  if(!open&&!tot)return"";
  const side=(id,n,pc)=>`<button class="pick${p.mine===id?" mine":""}" data-act="vote" data-m="${m.id}" data-t="${id}"${open&&uid?"":" disabled"}>${badge(id,22)}<span>${esc(tname(id))}${p.mine===id?" ✓":""}</span><b>${tot?pc+"%":"–"}</b></button>`;
  const head=open?(p.mine?"Prediction saved. Tap the other team to change it before the first ball.":"Who wins this match? Tap a team."):`Fans' prediction · ${tot} vote${tot===1?"":"s"}`;
  const nameBox=open&&p.mine&&!FAN.name?`<div class="kv">Optional: add your name to appear on the prediction leaderboard.</div><div class="prow"><input id="fan-name" placeholder="Your name" maxlength="30" data-fanname="1"><button class="btn sm" data-act="fanSave">Save</button></div>`:"";
  return`<div class="poll"><div class="label">${head}</div><div class="bar"><span style="width:${pa}%"></span></div><div class="picks">${side(m.a,ca,pa)}${side(m.b,cb,100-pa)}</div>${open&&tot?`<div class="kv">${tot} vote${tot===1?"":"s"} so far</div>`:""}${nameBox}</div>`;
}
/* ===== Tournament winner vote: one tap, changeable until the first ball of the tournament ===== */
let CUP={c:{},mine:null,at:0,final:false};
async function loadCup(force){
  if(!db||KIDS)return;if(!force&&CUP.at&&(CUP.final||Date.now()-CUP.at<180000))return;
  const locked=fantasyLocked();CUP.at=Date.now();
  try{const s=await getDoc(doc(db,C("cup"),"winner"));const d=s.exists()?s.data():{};const c={};for(const k in d)c[d[k]]=(c[d[k]]||0)+1;
    CUP={c,mine:uid?d[uid]||null:null,at:Date.now(),final:locked};scheduleRender()}catch(e){}
}
function cupHtml(){
  if(KIDS||!T||!T.teams.length)return"";
  if(!DEMO)loadCup();
  const open=!fantasyLocked(),champ=champion();
  const tot=Object.values(CUP.c).reduce((a,b)=>a+b,0);
  // Fixed order: Group A in the first row of 5, Group B in the second (2 per row on phones)
  const TM=(window.MASCON_TEAMS||[]).map(t=>t.name.toLowerCase());
  const ord=t=>{const i=TM.indexOf(String(t.name).toLowerCase());return i<0?99:i};
  const teams=[...T.teams].sort((a,b)=>String(a.group||"").localeCompare(String(b.group||""))||ord(a)-ord(b)||a.name.localeCompare(b.name));
  const head=open?(CUP.mine?`Your pick: <b>${esc(tname(CUP.mine))}</b>. Tap another team to change it before the first ball on 29 November.`:"Tap the team you think will lift the cup."):`Fans' pick to win the cup · ${tot} vote${tot===1?"":"s"}`;
  return`<div class="panel cupvote"><h2>Who will win the Mascon Cup?</h2><p class="kv">${head}</p><div class="cupgrid">${teams.map(t=>{const n=CUP.c[t.id]||0,pc=tot?Math.round(n*100/tot):0;
    return`<button class="cupt${CUP.mine===t.id?" mine":""}${champ===t.id?" won":""}" data-act="cupVote" data-t="${t.id}"${open&&(uid||DEMO)?"":" disabled"}>${badge(t.id,30)}<span>${esc(tname(t.id))}${CUP.mine===t.id?" ✓":""}</span>${tot?`<b>${pc}%</b><i style="width:${pc}%"></i>`:""}</button>`}).join("")}</div></div>`;
}
async function cupVote(team){
  if(fantasyLocked()){flash("Voting closed at the first ball.");return}
  if(DEMO){if(CUP.mine)CUP.c[CUP.mine]--;CUP.c[team]=(CUP.c[team]||0)+1;CUP.mine=team;render();flash(`Your pick to win the cup: ${tname(team)} (demo).`,true);return}
  if(!uid){flash("Voting needs a connection. Try again in a moment.");return}
  if(CUP.mine)CUP.c[CUP.mine]=Math.max(0,(CUP.c[CUP.mine]||1)-1);CUP.c[team]=(CUP.c[team]||0)+1;CUP.mine=team;render();
  try{await setDoc(doc(db,C("cup"),"winner"),{[uid]:team},{merge:true});flash(`Your pick to win the cup: ${tname(team)}.`,true)}
  catch(e){flash("Vote not saved. Voting closes at the first ball.");loadCup(true)}
}
async function vote(mid,team){
  if(!uid){flash("Predictions need a connection. Try again in a moment.");return}
  const p=polls[mid]||{c:{},mine:null,at:0};
  if(p.mine)p.c[p.mine]=Math.max(0,(p.c[p.mine]||1)-1);
  p.c[team]=(p.c[team]||0)+1;p.mine=team;polls[mid]=p;render();
  try{await setDoc(doc(db,C("polls"),mid),{[uid]:team},{merge:true});if(FAN.name)setDoc(doc(db,C("fans"),uid),{name:FAN.name,uid},{merge:true}).catch(()=>{});flash(`Prediction saved: ${tname(team)}.`,true);loadPoll(mid,true)}
  catch(e){flash("Prediction not saved. Voting closes at the first ball.");loadPoll(mid,true)}
}

/* ================= storage ================= */
function setSync(c,t){syncState={c:"sync"+(c==="err"?" err":""),t};const el=$("#sync");if(el){el.className=syncState.c;el.textContent=t}}
const strip=o=>JSON.parse(JSON.stringify(o));
function saveMatch(m){
  m.upd=Date.now();M[m.id]=m;
  if(!KIDS&&m.ph===undefined&&(m.inn||[]).some(i=>i.balls.length))m.ph=SUBS.phase||0;
  if(!fantasyLockWritten&&(m.inn||[]).some(i=>i.balls.length)){fantasyLockWritten=true;setDoc(doc(db,C("meta"),"lock"),{at:Date.now()}).then(()=>publishBoard()).catch(()=>{fantasyLockWritten=false})}
  try{sessionStorage.setItem(SK("mc-score"),ui.scoreSel||"")}catch(e){}
  render();
  setDoc(doc(db,C("matches"),m.id),strip(m)).then(()=>maybePublishBoard(m)).catch(e=>{setSync("err",e?.code==="permission-denied"?"Not saved: log in again":"Not saved");if(e?.code==="permission-denied"){canScore=false;render()}});
}
function delMatchDoc(id){deleteDoc(doc(db,C("matches"),id)).catch(()=>setSync("err","Delete failed"));deleteDoc(doc(db,C("polls"),id)).catch(()=>{})}

let DEMO_DATA=null,DEMO_DAY=0,DEMO_DAY_OF={};
async function demoBoot(){
  FT.myId=null;FT.mine=null;
  document.body.insertAdjacentHTML("afterbegin",`<div class="demobar"><b>DEMO PREVIEW</b> · demo squads · nothing is saved</div>`);
  try{const r=await fetch("demo.json",{cache:"no-store"});DEMO_DATA=await r.json()}catch(e){fatal="read";loaded={t:true,m:true};render();return}
  T={...DEF,...DEMO_DATA.tournament};
  // Start with every match unplayed so fantasy picks are open
  // Split the demo fixtures into 3 match days: first half of the league, second half, then knockouts
  const ms=Object.values(DEMO_DATA.matches).sort((a,b)=>(a.no||0)-(b.no||0));const lg=ms.filter(m=>m.stage==="A"||m.stage==="B"),half=Math.ceil(lg.length/2);
  const DAYS=["2026-11-29","2026-12-06","2026-12-13"];DEMO_DAY_OF={};
  ms.forEach(m=>{DEMO_DAY_OF[m.id]=lg.includes(m)?(lg.indexOf(m)<half?0:1):2});
  M={};ms.forEach(m=>M[m.id]={...m,status:"scheduled",inn:[],result:"",winner:null,toss:null,chose:null,when:DAYS[DEMO_DAY_OF[m.id]]+"T09:00"});
  DEMO_DAY=0;SUBS={phase:0,open:false};
  FT.all=(DEMO_DATA.fantasy||[]).map(f=>({id:f.id,name:f.name,p:f.p,c:f.p[0],vc:f.p[1]}));FAN.all={};FAN.polls={};
  loaded={t:true,m:true};ui.tab="fantasy";render();
}
function demoPlayDay(){
  if(!DEMO_DATA||DEMO_DAY>2)return;
  if(SUBS.open)SUBS={phase:SUBS.phase,open:false};          // first ball closes the window
  const ph=SUBS.phase;
  Object.values(DEMO_DATA.matches).forEach(m=>{if(DEMO_DAY_OF[m.id]===DEMO_DAY)M[m.id]={...m,ph,when:M[m.id].when}});
  DEMO_DAY++;FT.draft=null;
  if(DEMO_DAY<=2)SUBS={phase:ph+1,open:true};                // last match of the day ended: window opens
  ui.tab="fantasy";render();scrollTo(0,0);
  flash(DEMO_DAY<=2?`Match day ${DEMO_DAY} played. Substitution window open: make up to 2 changes before match day ${DEMO_DAY+1}.`:"Match day 3 played. Tournament over: see the final leaderboard.",true);
}
function boot(){
  if(DEMO){demoBoot();return}
  if(!CFG.firebase||!CFG.firebase.apiKey||CFG.firebase.apiKey==="PASTE_HERE"){fatal="config";loaded={t:true,m:true};render();return}
  const app=initializeApp(CFG.firebase);
  try{db=initializeFirestore(app,{localCache:persistentLocalCache({tabManager:persistentMultipleTabManager()})})}catch(e){db=getFirestore(app)}
  auth=getAuth(app);
  onAuthStateChanged(auth,u=>{
    uid=u?.uid||null;canScore=!!u&&!!u.email&&u.email===CFG.scorerEmail;if(canScore)loadSubs();
    if(!u)signInAnonymously(auth).catch(()=>{});
    for(const k in polls){polls[k].at=0;polls[k].final=false}CUP.at=0;
    if(!canScore&&(ui.tab==="score"||ui.tab==="setup"))ui.tab="live";
    render();
  });
  listen();
  // Fans' phones stop listening 30 s after the app goes to the background and catch up when reopened
  // (Firestore only charges for records that changed meanwhile). The scorer's phone always stays connected.
  document.addEventListener("visibilitychange",()=>{
    clearTimeout(hideTimer);
    if(document.hidden){if(!canScore)hideTimer=setTimeout(()=>{if(document.hidden&&!canScore)unlisten()},30000)}
    else listen();
  });
}
let unsubs=[],hideTimer=null;
function unlisten(){unsubs.forEach(u=>{try{u()}catch(e){}});unsubs=[]}
function listen(){
  if(!db||unsubs.length)return;
  unsubs.push(onSnapshot(doc(db,C("tournament"),"main"),s=>{T=s.exists()?{...DEF,...s.data()}:null;loaded.t=true;scheduleRender()},e=>{fatal="read";scheduleRender()}));
  unsubs.push(onSnapshot(collection(db,C("matches")),{includeMetadataChanges:true},s=>{
    const next={};s.docs.forEach(d=>next[d.id]=d.data());M=next;loaded.m=true;
    if(canScore){if(s.metadata.hasPendingWrites)setSync("",navigator.onLine?"Saving…":"Offline · saved on this phone");else if(!s.metadata.fromCache)setSync("","Synced")}
    scheduleRender();
  },e=>{fatal="read";scheduleRender()}));
}
const isTyping=()=>{const a=document.activeElement;return!!(a&&$("#app")?.contains(a)&&/INPUT|SELECT|TEXTAREA/.test(a.tagName))};
function scheduleRender(){if(isTyping()){renderDeferred=true;return}render()}
document.addEventListener("focusout",()=>setTimeout(()=>{if(renderDeferred&&!isTyping()){renderDeferred=false;render()}},60));
addEventListener("online",()=>canScore&&setSync("","Saving…"));
addEventListener("offline",()=>canScore&&setSync("","Offline · saved on this phone"));

/* ================= views ================= */
function headerHtml(){
  const t=KIDS?[["live","Live"],["matches","Matches"],["table","Table"],["stats","Stats"]]:[["live","Live"],["matches","Matches"],["table","Table"],["stats","Stats"],["fantasy","Fantasy"],["rules","Rules"]];
  if(canScore){t.push(["score","Score"]);t.push(["setup","Setup"])}
  const nm=(T?.name||DEF.name).replace(/\s*\(DEMO\)\s*/i,"").replace(/\s*kids\s*$/i,"");const demo=/DEMO/i.test(T?.name||"");
  const parts=nm.split(/\s+/);const eyebrow=parts.length>2?parts[0]:"";const main=parts.length>2?parts.slice(1).join(" "):nm;
  return`<div class="wrap"><div class="brand">${CFG.appLogo?`<img class="applogo" src="brand/${esc(CFG.appLogo)}" alt="">`:`<span class="mark" aria-hidden="true"></span>`}<h1>${eyebrow?`<small>${esc(eyebrow)}${KIDS?" · KIDS":""}${demo?" · DEMO":""}</small>`:""}${esc(main)}</h1><span class="${syncState.c}" id="sync">${esc(canScore?syncState.t:"")}</span>${canScore||DEMO?"":`<button class="btn sm ghost" data-act="tab" data-v="login">Scorer</button>`}</div>
  <div class="cupsw" role="tablist" aria-label="Tournament"><a href="${location.pathname}" aria-current="${!KIDS}">Adults</a><a href="${location.pathname}?cup=kids" aria-current="${KIDS}">Kids</a></div>
  <nav class="tabs" aria-label="Sections">${t.map(([k,l])=>`<button data-act="tab" data-v="${k}" aria-current="${ui.tab===k}">${l}</button>`).join("")}</nav></div>${sponsorHtml()}`;
}
function welcomeShow(){
  const w=CFG.welcome;if(!w)return;let seen=w.enabled===false;try{seen=sessionStorage.getItem("mc-welcome")==="1"}catch(e){}
  try{if(new URLSearchParams(location.search).get("welcome")==="1")seen=false}catch(e){}
  if(seen)return;
  const el=document.createElement("div");el.className="welcome";el.setAttribute("role","dialog");el.setAttribute("aria-label","Welcome");
  const sp=(w.sponsors||[]).filter(s=>s&&(s.name||s.logo||s.names));
  el.innerHTML=`<div class="wl-in">${CFG.appLogo?`<img class="wl-logo" src="brand/${esc(CFG.appLogo)}" alt="">`:`<span class="mark wl-mark" aria-hidden="true"></span>`}
    ${w.organiser?`<span class="wl-org">${esc(w.organiser)}</span>`:""}<h2 class="wl-title">${esc(w.title||"")}</h2>${w.message?`<p class="wl-msg">${esc(w.message)}</p>`:""}
    ${sp.length?`<div class="wl-sp">${sp.map((s,i)=>`<div class="wl-s${i===0?" main":""}"><span class="wl-role">${esc(s.role||"")}</span>${s.logo?`<span class="wl-tile${s.dark?" dark":""}"><img src="brand/${esc(s.logo)}" alt="${esc(s.name||"")}"></span>${s.sub?`<b>${esc(s.sub)}</b>`:""}`:(s.names||[s.name]).map(n=>`<b>${esc(n||"")}</b>`).join("")}</div>`).join("")}</div>`:""}
    <button class="btn pri wl-go" type="button">See live scores</button><div class="wl-bar"><span style="animation-duration:${(+w.seconds||5)}s"></span></div></div>`;
  document.body.appendChild(el);document.documentElement.classList.add("wl-open");
  const close=()=>{if(!el.isConnected)return;el.classList.add("out");document.documentElement.classList.remove("wl-open");setTimeout(()=>el.remove(),350);try{sessionStorage.setItem("mc-welcome","1")}catch(e){}};
  el.querySelector(".wl-go").addEventListener("click",close);
  if(+w.seconds>0)setTimeout(close,(+w.seconds)*1000);
}
function sponsorHtml(){
  const sp=(CFG.sponsors||[]).filter(x=>x&&x.name);if(!sp.length)return"";
  return`<div class="sponsors"><div class="wrap"><span class="label">Presented by</span>${sp.map(x=>x.logo?`<img src="${esc(x.logo)}" alt="${esc(x.name)}">`:`<span class="spn">${esc(x.name)}</span>`).join("")}</div></div>`;
}
const fmtWhen=w=>{if(!w)return"";const d=new Date(w);if(isNaN(d))return"";return d.toLocaleString("en-IN",{weekday:"short",day:"numeric",month:"short",hour:"numeric",minute:"2-digit"})};
const fmtDay=w=>{if(!w)return"Date to be announced";const d=new Date(w);if(isNaN(d))return"Date to be announced";return d.toLocaleDateString("en-IN",{weekday:"long",day:"numeric",month:"long"})};
const fmtTime=w=>{if(!w)return"";const d=new Date(w);return isNaN(d)?"":d.toLocaleTimeString("en-IN",{hour:"numeric",minute:"2-digit"})};
const stageLabel=m=>`${STAGES[m.stage]||""}${isLeague(m)?" · Match "+m.no:""}${m.pitch?" · "+m.pitch:""}`;
function statusPill(m){
  return m.status==="live"?`<span class="pill live">Live</span>`:m.status==="break"?`<span class="pill live">Innings break</span>`:m.status==="super"?`<span class="pill live">Super Over</span>`
    :m.status==="done"?`<span class="pill done">Result</span>`:m.status==="setup"?`<span class="pill live">Toss done</span>`:`<span class="pill up">Upcoming</span>`;
}
function boardHtml(m){
  const meta=`<div class="meta">${statusPill(m)}<span>${esc(stageLabel(m))}</span><span>· ${mOvers(m)} overs</span></div>`;
  const vs=`<div class="vsrow"><div class="vst" data-act="team" data-id="${m.a}">${badge(m.a,56)}<b>${esc(tname(m.a))}</b></div><span class="vsx">vs</span><div class="vst" data-act="team" data-id="${m.b}">${badge(m.b,56)}<b>${esc(tname(m.b))}</b></div></div>`;
  if(m.status==="scheduled")return`<div class="board">${meta}${vs}<div class="small" style="color:var(--board-muted);text-align:center">${m.when?esc(fmtWhen(m.when)):"Toss not done yet."}</div></div>`;
  if(!m.inn.length){
    const done=m.status==="done";
    return`<div class="board">${meta}${vs}${done?`<div class="result">${esc(m.result)}</div>`:`<div class="small" style="color:var(--board-muted);text-align:center">${esc(tname(m.toss))} won the toss and chose to ${m.chose==="bat"?"bat":"bowl"}. Openers coming out.</div>`}</div>`;
  }
  const i=m.inn.length-1,inn=m.inn[i],st=innStats(inn),tg=targetOf(m),ov=ovFor(m,i);
  const s1=m.inn.length>1?innStats(m.inn[0]):null;
  const line=(tid,sc,ovs_,on)=>`<div class="tm${on?" on":""}" data-act="team" data-id="${tid}">${badge(tid,40)}<div class="tmn"><b>${esc(tname(tid))}</b>${sc!==null?`<span>${sc}<small> (${ovs_})</small></span>`:`<span class="muted small">yet to bat</span>`}</div></div>`;
  const first=m.inn[0].bat,second=first===m.a?m.b:m.a;
  const strip=`<div class="teams">${line(first,m.inn.length>1?s1.runs+"/"+s1.wk:st.runs+"/"+st.wk,m.inn.length>1?ovs(s1.legal):ovs(st.legal),m.inn.length===1)}${line(second,m.inn.length>1?st.runs+"/"+st.wk:null,m.inn.length>1?ovs(st.legal):"",m.inn.length>1)}</div>`;
  let chase="";
  if(m.status==="done"||m.status==="super"){const mv=m.status==="done"?matchMvp(m):null;chase=`<div class="result">${esc(m.result)}</div>${mv?`<div class="pom" data-act="player" data-id="${mv.id}">${badge(pteam(mv.id),28)}<span><small>Player of the match</small><b>${esc(pname(mv.id))}</b></span><span class="pts">${mv.pts} pts</span></div>`:""}`}
  else if(m.status==="break")chase=`<div class="chase">${esc(tname(inn.bowl))} need ${st.runs+1} to win off ${ovFor(m,1)} overs</div>`;
  else if(tg){const need=tg-st.runs,left=ov*6-st.legal;chase=`<div class="chase">${esc(tname(inn.bat))} need ${need} run${need===1?"":"s"} from ${left} ball${left===1?"":"s"}</div>`}
  const rates=m.status==="live"?`<div class="rates"><span>Run rate <b>${rate(st.runs,st.legal)}</b></span>${tg?`<span>Required <b>${rate(tg-st.runs,ov*6-st.legal)}</b></span><span>Target <b>${tg}</b>${m.tgt?" (revised)":""}</span>`:""}</div>`:"";
  let crease="",overRow="",flags="";
  if(m.status==="live"){
    const bl=id=>{if(!id)return"";const b=st.bat[id]||{r:0,b:0,f:0,s:0};return`<span class="nm">${esc(pname(id))}${id===inn.cur.s?" *":""}</span><span class="fig"><b>${b.r}</b> (${b.b})${b.f||b.s?` · ${b.f}×4 ${b.s}×6`:""}</span>`};
    const bwId=inn.cur.bw||last(inn.balls)?.bw,bw=bwId?st.bowl[bwId]||{l:0,r:0,w:0}:null;
    crease=`<div class="crease">${bl(inn.cur.s)}${bl(inn.cur.ns)}${bw?`<span class="nm bowl">${esc(pname(bwId))} (bowling)</span><span class="fig"><b>${bw.w}-${bw.r}</b> (${ovs(bw.l)})</span>`:""}</div>`;
    const n=Math.floor(st.legal/6)+1,tag=n<=ov?overTag(ov,n):"";
    overRow=`<div class="over"><span class="label">Over ${n}</span>${tag?`<span class="pill sp">${tag}</span>`:""}${st.cur.map(chip).join("")}</div>`;
    if(isFreeHit(inn))flags+=`<span class="flag">Free hit</span>`;
    if(st.legal===Math.floor(ov/2)*6&&!st.cur.length&&st.legal>0)flags+=`<span class="flag">Halfway: batting end changes</span>`;
  }
  const big=m.status==="live"?`<div class="score-row"><div class="score-big">${st.runs}<small>/${st.wk}</small></div><div class="score-ov">${ovs(st.legal)} <span>/ ${ov} ov</span></div></div>`:"";
  return`<div class="board">${meta}${strip}${big}${chase}${rates}${crease}${overRow}${flags}</div>`;
}
function feedText(b){
  const who=`<b>${esc(pname(b.bw))}</b> to <b>${esc(pname(b.s))}</b>`;let d;
  if(b.t==="run")d=b.r===0?"no run":b.r===4?"<b class=\"four\">FOUR</b>":b.r===6?"<b class=\"six\">SIX</b>":b.r+" run"+(b.r>1?"s":"");
  else if(b.t==="wd")d="wide"+(b.r?`, ${b.r} run${b.r>1?"s":""} taken`:"");
  else if(b.t==="nb")d="no ball"+(b.r?`, ${b.r===4?"<b class=\"four\">FOUR</b>":b.r===6?"<b class=\"six\">SIX</b>":b.r+" run"+(b.r>1?"s":"")} off the bat`:"");
  else d=`${b.r} ${b.t==="bye"?"bye":"leg bye"}${b.r>1?"s":""}`;
  if(invalidW(b))d+=` <span class="bad">· wicket ignored: ${b.t==="nb"?"no ball":b.fh?"free hit":"wide"}, ${b.t==="wd"?"run out or stumped":"run out"} only</span>`;
  if(validW(b)){const w=b.w,f=w.f?pname(w.f):"";const how=w.k==="c"?(w.f===b.bw?"caught and bowled":f?`caught by ${f}`:"caught"):w.k==="b"?"bowled":w.k==="ro"?(f?`run out by ${f}`:"run out"):w.k==="st"?`stumped${f?" by "+f:""}`:w.k==="lbw"?"lbw":w.k==="hw"?"hit wicket":"out";
    d=`<b class="outx">OUT</b> ${esc(pname(w.out))} ${esc(how)}${b.r?` (${b.r} run${b.r>1?"s":""} completed)`:""}${b.t==="wd"?" (wide)":b.t==="nb"?" (no ball)":""}`}
  return`${who}, ${d}${b.fh?" · free hit":""}<span class="ns">non-striker ${esc(pname(b.ns))}</span>`;
}
function feedHtml(m){
  const msByBall=new Map();milestones(m).forEach(x=>{const b=m.inn[x.ii].balls[x.idx];if(!msByBall.has(b))msByBall.set(b,[]);msByBall.get(b).push(x)});
  // group balls by over, newest over first, with an end-of-over summary (bowler, runs, score, batters)
  const blocks=[];
  m.inn.forEach((inn,ii)=>{
    const st=innStats(inn);let runs=0,wk=0,bat={},cur=[],ovNo=1;let scoreAfter=0,wkAfter=0;
    const flush=(complete)=>{if(!cur.length)return;const bw=cur[0].b.bw;const bs=cur.map(e=>e.b);const ovRuns=bs.reduce((a,b)=>a+ballRuns(b),0),ovWk=bs.filter(b=>validW(b)).length;
      const lastB=last(cur).b;const batters=[lastB.s,lastB.ns].filter(Boolean).map(id=>{const x=bat[id]||{r:0,b:0};return`${esc(pname(id))} ${x.r} (${x.b})`}).join(" · ");
      const bowlRuns=bs.reduce((a,b)=>a+(b.t==="bye"||b.t==="lb"?0:ballRuns(b)),0);const bowlTot=st.bowl[bw]||{l:0,r:0,w:0};
      blocks.push({ii,ovNo,complete,bw,ovRuns,ovWk,scoreAfter,wkAfter,batters,bowlRuns,bowlTot,balls:cur.slice().reverse(),bat:tmeta(inn.bat).short});cur=[]};
    inn.balls.forEach((b,idx)=>{const before=st.log[idx];runs+=ballRuns(b);if(validW(b))wk++;
      const bt=bat[b.s]||(bat[b.s]={r:0,b:0});if(b.t==="run"||b.t==="nb")bt.r+=b.r;if(b.t!=="wd")bt.b++;
      cur.push(before);scoreAfter=runs;wkAfter=wk;
      const legal=inn.balls.slice(0,idx+1).filter(isLegal).length;if(isLegal(b)&&legal%6===0){flush(true);ovNo=legal/6+1}});
    flush(false);
  });
  if(!blocks.length)return"";
  const recent=blocks.slice(-4).reverse();
  return`<div><div class="label">Ball by ball</div><div class="feed">${recent.map(o=>`
    <div class="ovhead${o.complete?"":" open"}"><div class="ovh1"><span><b>${o.complete?"End of over "+o.ovNo:"Over "+o.ovNo}</b> · ${o.ovRuns} run${o.ovRuns===1?"":"s"}${o.ovWk?` · ${o.ovWk} wkt`:""}</span><b class="sc">${esc(o.bat)} ${o.scoreAfter}/${o.wkAfter}</b></div>
    <div class="ovh2"><span>${o.batters}</span><span>${esc(pname(o.bw))} ${o.bowlTot.w}-${o.bowlTot.r} (${ovs(o.bowlTot.l)})</span></div></div>
    ${o.balls.map(e=>{const ms=msByBall.get(e.b);return`<div class="row${validW(e.b)?" wk":""}${ms?" ms":""}"><span class="ov">${e.lab}</span>${chip(e.b)}<span class="txt">${feedText(e.b)}${ms?ms.map(x=>`<span class="msl">${MS_ICON[x.type]} ${esc(x.text)}</span>`).join(""):""}</span></div>`}).join("")}`).join("")}</div>${blocks.length>4?`<p class="kv">Showing the last 4 overs. Full details are in the scorecard.</p>`:""}</div>`;
}
function cardHtml(m,i,open){
  const inn=m.inn[i],st=innStats(inn),live=m.status==="live"&&!inn.closed;
  const bat=st.batOrder.map(id=>{const b=st.bat[id],at=live&&(id===inn.cur.s||id===inn.cur.ns);
    return`<tr><td class="n"><span class="plink" data-act="player" data-id="${id}">${esc(pname(id))}</span><span class="how">${b.out?esc(b.out):at?"batting":"not out"}</span></td><td><b>${b.r}</b></td><td>${b.b}</td><td>${b.f}</td><td>${b.s}</td><td>${b.b?(b.r*100/b.b).toFixed(0):"–"}</td></tr>`}).join("");
  const yet=xiPlayers(m,inn.bat).filter(p=>!st.bat[p.id]).map(p=>esc(p.name));
  const exT=st.ex.wd+st.ex.nb+st.ex.b+st.ex.lb;
  const bowl=st.bowlOrder.map(id=>{const b=st.bowl[id];return`<tr><td class="n"><span class="plink" data-act="player" data-id="${id}">${esc(pname(id))}</span></td><td>${ovs(b.l)}</td><td>${b.r}</td><td><b>${b.w}</b></td><td>${rate(b.r,b.l)}</td><td>${b.wd}/${b.nb}</td></tr>`}).join("");
  return`<details class="card"${open?" open":""}><summary><span>${esc(tname(inn.bat))} · ${i===0?"1st":"2nd"} innings</span><span class="sc">${st.runs}/${st.wk} <span class="muted small">(${ovs(st.legal)})</span></span></summary><div class="in">
  <div class="tbl"><table><thead><tr><th>Batter</th><th>R</th><th>B</th><th>4s</th><th>6s</th><th>SR</th></tr></thead><tbody>${bat||`<tr><td colspan="6" class="muted">No balls bowled yet</td></tr>`}
  <tr><td>Extras <span class="how">wd ${st.ex.wd}, nb ${st.ex.nb}, b ${st.ex.b}${st.ex.lb?", lb "+st.ex.lb:""}</span></td><td>${exT}</td><td colspan="4"></td></tr>
  <tr class="tot"><td>Total</td><td>${st.runs}/${st.wk}</td><td colspan="4" class="muted">${ovs(st.legal)} ov · RR ${rate(st.runs,st.legal)}</td></tr></tbody></table></div>
  ${yet.length?`<div class="kv"><b>Yet to bat:</b> ${yet.join(", ")}</div>`:""}
  ${st.fow.length?`<div class="kv"><b>Fall of wickets:</b> ${st.fow.map(f=>`${f.r}-${f.n} (${esc(pname(f.id))}, ${f.ov})`).join(", ")}</div>`:""}
  <div class="tbl"><table><thead><tr><th>Bowler</th><th>O</th><th>R</th><th>W</th><th>Econ</th><th>Wd/Nb</th></tr></thead><tbody>${bowl||`<tr><td colspan="6" class="muted">—</td></tr>`}</tbody></table></div>
  </div></details>`;
}
function shareText(m){
  const s=i=>{const x=innStats(m.inn[i]);return`${tname(m.inn[i].bat)} ${x.runs}/${x.wk} (${ovs(x.legal)})`};
  const lines=[`*${(T?.name||DEF.name).replace(/\s*\(DEMO\)/i,"")}* · ${stageLabel(m)}`];
  if(m.inn?.length){lines.push(s(0));if(m.inn[1])lines.push(s(1))}
  if(m.result)lines.push(`*${m.result}*`);
  const mv=m.status==="done"?matchMvp(m):null;if(mv)lines.push(`Player of the match: ${pname(mv.id)}`);
  if(m.status==="live"){const i=m.inn.length-1,st=innStats(m.inn[i]);const tg=targetOf(m);if(tg)lines.push(`Need ${tg-st.runs} from ${ovFor(m,i)*6-st.legal} balls`)}
  if(typeof location!=="undefined"&&location.origin)lines.push(location.origin+location.pathname+(KIDS?"?cup=kids":""));return lines.join("\n");
}
function shareBtn(m){return`<a class="btn sm wa" href="https://wa.me/?text=${encodeURIComponent(shareText(m))}" target="_blank" rel="noopener">Share on WhatsApp</a>`}
function msStrip(m){const l=milestones(m);if(!l.length)return"";
  return`<div><div class="label">Milestones</div><div class="mslist">${l.slice().reverse().map(x=>`<span class="msc"><span>${MS_ICON[x.type]}</span>${esc(x.text)}</span>`).join("")}</div></div>`}
function matchDetail(m){
  return`${boardHtml(m)}<div class="row-btns">${shareBtn(m)}${m.status==="done"&&m.inn?.length?`<button class="btn sm" data-act="card" data-id="${m.id}">Result card image</button>`:""}</div>${msStrip(m)}${pollHtml(m)}${feedHtml(m)}
  ${m.inn.length?`<div class="label">Scorecard</div>`+m.inn.map((_,i)=>cardHtml(m,i,i===m.inn.length-1)).join(""):""}
  ${m.super?`<div class="kv"><b>Super Over:</b> ${esc(m.super)}</div>`:""}`;
}
const byNo=(a,b)=>(a.no||0)-(b.no||0);
function champion(){const f=Object.values(M).find(m=>m.stage==="F"&&m.status==="done"&&m.winner&&m.winner!=="tie"&&m.winner!=="nr");return f?f.winner:null}
function miniTable(g){const rows=pointsTable(g).slice(0,5);if(!rows.length||!rows.some(r=>r.p))return"";
  return`<div class="mini"><div class="label">Group ${g}</div>${rows.map((r,i)=>`<div class="mr${i<3?" q":""}" data-act="team" data-id="${r.id}">${badge(r.id,22)}<span class="tn">${esc(tmeta(r.id).short)}</span><span class="muted">${r.p}</span><b>${r.pts}</b><span class="nrr">${(r.nrr>=0?"+":"")+r.nrr.toFixed(2)}</span></div>`).join("")}</div>`}
function topCards(){const{bat,bowl}=tourStats();const b=Object.entries(bat).sort((a,b)=>b[1].r-a[1].r)[0],w=Object.entries(bowl).sort((a,b)=>b[1].w-a[1].w||a[1].r-b[1].r)[0];
  const mv=mvpTable()[0],em=KIDS?null:mvpTable(id=>{const g=pAge(id);return g&&g<=(T.emergingAge||DEF.emergingAge)})[0];
  if(!b)return"";const card=(lab,id,val,unit,stat)=>`<button class="tcard" data-act="statTab" data-v="${stat}">${badge(pteam(id),30)}<span class="lab">${lab}</span><b>${esc(pname(id))}</b><span class="val">${val}<small> ${unit}</small></span></button>`;
  return`<div class="label">Leading the tournament</div><div class="tcards">${mv?card("MVP",mv.id,mv.pts,"pts","mvp"):""}${em?card("Emerging player",em.id,em.pts,"pts","emerging"):""}${card("Most runs",b[0],b[1].r,"runs","runs")}${w?card("Most wickets",w[0],w[1].w,"wkts","wkts"):""}</div>`}
function liveView(){
  if(!T)return`<section><div class="empty"><strong>${KIDS?"Kids' matches will show here":"Scores start on 29 November"}</strong>${canScore?"Open Setup to add the ten teams and their squads.":"Live scores, scorecards, the points table and player stats appear here once the tournament begins."}</div></section>`;
  const list=Object.values(M);
  const live=list.filter(m=>LIVE.includes(m.status)).sort((a,b)=>(b.upd||0)-(a.upd||0));
  const m=(ui.sel&&M[ui.sel])||live[0];
  if(m){
    const others=live.filter(x=>x.id!==m.id);
    return`<section>${ui.sel&&!live.includes(m)?`<button class="btn sm" data-act="unsel">← Back</button>`:""}${matchDetail(m)}
    ${others.length?`<div class="row-btns">${others.map(o=>`<button class="btn sm" data-act="view" data-id="${o.id}">Also live: ${esc(tname(o.a))} v ${esc(tname(o.b))}</button>`).join("")}</div>`:""}</section>`;
  }
  const next=list.filter(x=>x.status==="scheduled").sort((x,y)=>(x.when||"9")<(y.when||"9")?-1:(x.when||"9")>(y.when||"9")?1:byNo(x,y))[0];
  const done=list.filter(x=>x.status==="done").sort((a,b)=>(b.upd||0)-(a.upd||0)||(b.no||0)-(a.no||0));
  const champ=champion();
  if(!next&&!done.length)return`<section>${miniTable("A")?"":""}<div class="empty"><strong>No match in progress</strong>${canScore?"Open Score to start a match.":"The next match will show here live, ball by ball."}</div></section>`;
  const hero=champ?`<div class="board champ"><div class="meta"><span class="pill done">Champions</span><span>${esc(STAGES.F)}</span></div><div class="champ-in" data-act="team" data-id="${champ}">${badge(champ,84)}<div><div class="champ-name">${esc(tname(champ))}</div><div class="small" style="color:var(--board-muted)">${esc(done.find(x=>x.stage==="F")?.result||"")}</div></div></div><button class="btn sm ghost" data-act="view" data-id="${done.find(x=>x.stage==="F")?.id}">Final scorecard</button></div>`
    :next?`<div class="label">Next match</div>${boardHtml(next)}${pollHtml(next)}`:"";
  const recent=done.slice(0,champ?2:3);
  return`<section>${hero}
  ${champ?"":cupHtml()}
  ${recent.length?`<div class="label">${champ?"Recent results":"Latest results"}</div><div class="mlist">${recent.map(matchRow).join("")}</div>`:""}
  ${done.length?`<div class="minis">${miniTable("A")}${miniTable("B")}</div><button class="btn sm" data-act="tab" data-v="table">Full points table</button>`:""}
  ${topCards()}
  ${sponsorsBlock()}
  </section>`;
}
function matchRow(m){
  const sc=id=>{const i=m.inn.findIndex(x=>x.bat===id);if(i<0)return"";const s=innStats(m.inn[i]);return`${s.runs}/${s.wk} (${ovs(s.legal)})`};
  const first=m.inn[0]?.bat||m.a,second=first===m.a?m.b:m.a;
  const win=m.winner&&m.winner!=="tie"&&m.winner!=="nr"?m.winner:null;
  return`<div class="mrow"><button class="mlink" data-act="view" data-id="${m.id}"><div class="top"><span class="label">${esc(stageLabel(m))}${m.when&&m.status==="scheduled"?` · ${esc(fmtTime(m.when))}`:""}</span>${statusPill(m)}</div><div class="t${win===first?" w":""}">${teamLine(first,"")}<span>${sc(first)}</span></div><div class="t${win===second?" w":""}">${teamLine(second,"")}<span>${sc(second)}</span></div>${m.result?`<div class="res">${esc(m.result)}</div>`:""}</button>${m.status==="scheduled"?pollHtml(m):""}</div>`;
}
function matchesView(){
  if(!T)return liveView();
  const list=Object.values(M).sort(byNo);
  if(!list.length)return`<section><div class="empty"><strong>Fixtures not out yet</strong>League fixtures appear here once the teams are set.</div></section>`;
  const ko=list.filter(m=>!isLeague(m)),lg=list.filter(isLeague),live=list.filter(m=>LIVE.includes(m.status));
  const block=(title,arr)=>arr.length?`<h2>${title}</h2><div class="mlist">${arr.map(matchRow).join("")}</div>`:"";
  const up=list.filter(m=>m.status==="scheduled"&&!live.includes(m)).sort((x,y)=>(x.when||"9")<(y.when||"9")?-1:(x.when||"9")>(y.when||"9")?1:byNo(x,y));
  const days={};up.forEach(m=>{const k=m.when?m.when.slice(0,10):"tba";(days[k]||(days[k]=[])).push(m)});
  const upBlocks=Object.entries(days).map(([k,arr])=>block(k==="tba"?"Upcoming · date to be announced":fmtDay(arr[0].when),arr)).join("");
  const results=list.filter(m=>m.status==="done").sort((x,y)=>byNo(y,x));
  return`<section>${block("Live now",live)}${upBlocks}${block("Results",results)}</section>`;
}
function groupTable(g){
  const rows=pointsTable(g);if(!rows.length)return"";
  const tnr=rows.some(r=>r.t||r.nr);
  return`<h2>Group ${g}</h2><div class="tbl"><table class="pts"><thead><tr><th>Team</th><th>P</th><th>W</th><th>L</th>${tnr?"<th>T/NR</th>":""}<th>Pts</th><th>NRR</th></tr></thead><tbody>${rows.map((r,i)=>`<tr${i<3&&r.p?' class="q"':""}><td class="n"><span class="tl" data-act="team" data-id="${r.id}">${badge(r.id,24)}<span class="tn"><b>${esc(tname(r.id))}</b>${tmeta(r.id).sponsor?`<span class="tsp">${esc(tmeta(r.id).sponsor)}</span>`:""}</span></span>${r.p&&i===0?'<span class="tag">SF</span>':r.p&&i<3?'<span class="tag">QF</span>':""}</td><td>${r.p}</td><td>${r.w}</td><td>${r.l}</td>${tnr?`<td>${r.t+r.nr||""}</td>`:""}<td><b>${r.pts}</b></td><td>${(r.nrr>=0?"+":"")+r.nrr.toFixed(2)}</td></tr>`).join("")}</tbody></table></div>`;
}
function tableView(){
  if(!T)return liveView();
  return`<section>${groupTable("A")}${groupTable("B")}<p class="kv">Win ${T.ptsWin} pts · tie or no result ${T.ptsTie} pt each. Group toppers go straight to the semi-finals; 2nd and 3rd play the quarter-finals (A2 v B3, B2 v A3). Teams level on points are split by net run rate, where an all-out side counts its full overs.</p></section>`;
}
function podium(rows,lab){
  if(!rows.length)return"";const top=rows.slice(0,3);const order=[top[1],top[0],top[2]].filter(Boolean);
  return`<div class="podium">${order.map(r=>{const rank=rows.indexOf(r)+1;return`<div class="pod r${rank}" data-act="player" data-id="${r.id}">${badge(pteam(r.id),rank===1?56:44)}<span class="rk">${rank===1?"🏆":"#"+rank}</span><b>${esc(pname(r.id))}</b><span class="muted small">${esc(tmeta(pteam(r.id)).short)}${pAge(r.id)?" · "+pAge(r.id)+" yrs":""}</span><span class="val">${r.pts}<small> ${lab}</small></span></div>`}).join("")}</div>`;
}
function statsView(){
  if(!T)return liveView();
  const{bat,bowl}=tourStats();
  const chips=[["mvp","MVP"],...(KIDS?[]:[["emerging","Emerging"]]),["runs","Most runs"],["wkts","Most wickets"],["sixes","Most sixes"],["fours","Most fours"]].map(([k,l])=>`<button class="opt" data-act="stat" data-v="${k}" aria-pressed="${ui.stat===k}">${l}</button>`).join("");
  const nm=id=>`<td class="n"><span class="tl" data-act="player" data-id="${id}">${badge(pteam(id),24)}<span class="tn"><b>${esc(pname(id))}</b><span class="how">${esc(tmeta(pteam(id)).short)}${pAge(id)?" · "+pAge(id):""}</span></span></span></td>`;
  let body="",head="",note="";
  if(ui.stat==="mvp"||ui.stat==="emerging"){
    const em=ui.stat==="emerging";const rows=mvpTable(em?id=>{const g=pAge(id);return g&&g<=(T.emergingAge||DEF.emergingAge)}:null);
    head=podium(rows,"pts");
    body=rows.length?`<table><thead><tr><th>#</th><th>Player</th><th>Pts</th><th>M</th><th>R</th><th>W</th><th>Ct</th></tr></thead><tbody>${rows.slice(0,25).map((r,i)=>`<tr${i<3?' class="q"':""}><td style="text-align:left">${i+1}</td>${nm(r.id)}<td><b>${r.pts}</b></td><td>${r.m}</td><td>${r.r}</td><td>${r.w}</td><td>${r.f}</td></tr>`).join("")}</tbody></table>`:"";
    note=em?`Emerging player: aged ${T.emergingAge||DEF.emergingAge} or under at registration, ranked by MVP points.`:"MVP points: run 1, four +1, six +2, 30 runs +4, 50 runs +8, duck −2, wicket 25, 3-wicket haul +8, catch/stumping/run-out 8, dot ball 1, maiden 12.";
  }else if(ui.stat==="wkts"){
    const rows=Object.entries(bowl).filter(([,x])=>x.l>0).sort((a,b)=>b[1].w-a[1].w||(a[1].r*6/a[1].l)-(b[1].r*6/b[1].l)).slice(0,20);
    body=rows.length?`<table><thead><tr><th>Bowler</th><th>W</th><th>O</th><th>R</th><th>Econ</th><th>Best</th></tr></thead><tbody>${rows.map(([id,x])=>`<tr>${nm(id)}<td><b>${x.w}</b></td><td>${ovs(x.l)}</td><td>${x.r}</td><td>${rate(x.r,x.l)}</td><td>${x.bw}/${x.br}</td></tr>`).join("")}</tbody></table>`:"";
  }else{
    const key=ui.stat==="sixes"?"s":ui.stat==="fours"?"f":"r";
    const rows=Object.entries(bat).filter(([,x])=>(key==="r"?x.b>0||x.r>0:x[key]>0)).sort((a,b)=>b[1][key]-a[1][key]||b[1].r-a[1].r||a[1].b-b[1].b).slice(0,20);
    const cols=key==="s"?[["6s","s"],["R","r"],["4s","f"]]:key==="f"?[["4s","f"],["R","r"],["6s","s"]]:[["R","r"],["6s","s"],["4s","f"]];
    body=rows.length?`<table><thead><tr><th>Batter</th>${cols.map(c=>`<th>${c[0]}</th>`).join("")}<th>Inn</th><th>HS</th><th>SR</th></tr></thead><tbody>${rows.map(([id,x])=>`<tr>${nm(id)}${cols.map((c,i)=>`<td>${i?x[c[1]]:`<b>${x[c[1]]}</b>`}</td>`).join("")}<td>${x.inns}</td><td>${x.hs}${x.hsNo?"*":""}</td><td>${x.b?(x.r*100/x.b).toFixed(0):"–"}</td></tr>`).join("")}</tbody></table>`:"";
  }
  return`<section><h2>Player stats</h2><div class="opts">${chips}</div>${head}${body?`<div class="tbl">${body}</div>`:`<div class="empty"><strong>No stats yet</strong>Leaders appear after the first ball is bowled.</div>`}<p class="kv">${note||"Across all matches including knockouts. Updates live."}</p></section>`;
}
function teamView(){
  const id=ui.teamId,t=teamOf(id);if(!t)return liveView();
  const me=tmeta(id);const list=Object.values(M).filter(m=>m.a===id||m.b===id).sort(byNo);
  const played=list.filter(m=>m.status==="done"),up=list.filter(m=>m.status!=="done");
  const row=pointsTable(t.group).find(r=>r.id===id);const pos=pointsTable(t.group).findIndex(r=>r.id===id)+1;
  const{bat,bowl}=tourStats();const pts=fantasyPoints();
  const squad=t.players.map(p=>({p,r:bat[p.id]?.r||0,b:bat[p.id]?.b||0,w:bowl[p.id]?.w||0,o:bowl[p.id]?.l||0,pts:pts[p.id]||0})).sort((x,y)=>y.pts-x.pts||y.r-x.r);
  const icon=(PRESET.find(x=>x.name===t.name.trim().toUpperCase())||PRESET.find(x=>x.name.split(" ")[0]===t.name.trim().toUpperCase().split(" ")[0]))?.icon;
  return`<section><button class="btn sm" data-act="tab" data-v="live">← Back</button>
  <div class="board" style="background:linear-gradient(160deg,${me.color} -40%,var(--board) 55%)"><div class="teamhero">${badge(id,96)}<div><div class="champ-name">${esc(t.name)}</div>${me.sponsor?`<div class="tspon">Sponsored by <b>${esc(me.sponsor)}</b></div>`:""}<div class="small" style="color:var(--board-muted)">Group ${t.group}${icon?` · Icon: ${esc(icon)}`:""}</div>${row&&row.p?`<div class="rates"><span>Position <b>#${pos}</b></span><span>Played <b>${row.p}</b></span><span>Won <b>${row.w}</b></span><span>Pts <b>${row.pts}</b></span><span>NRR <b>${(row.nrr>=0?"+":"")+row.nrr.toFixed(2)}</b></span></div>`:""}</div></div></div>
  ${up.length?`<h2>Fixtures</h2><div class="mlist">${up.map(matchRow).join("")}</div>`:""}
  ${played.length?`<h2>Results</h2><div class="mlist">${played.slice().reverse().map(matchRow).join("")}</div>`:""}
  <h2>Squad</h2><div class="tbl"><table><thead><tr><th>Player</th><th>Role</th><th>R</th><th>W</th><th>MVP</th></tr></thead><tbody>${squad.map(x=>`<tr><td class="n"><b class="plink" data-act="player" data-id="${x.p.id}">${esc(x.p.name)}</b>${x.p.age?`<span class="how">${x.p.age} yrs</span>`:""}</td><td>${esc(x.p.role||"")}</td><td>${x.r}${x.b?`<span class="muted small"> (${x.b})</span>`:""}</td><td>${x.w}${x.o?`<span class="muted small"> (${ovs(x.o)})</span>`:""}</td><td><b>${x.pts}</b></td></tr>`).join("")}</tbody></table></div></section>`;
}
/* ================= player profile ================= */
function playerLine(m,id){
  const team=pteam(id);const r={m,bat:null,notOut:false,bowl:null,ct:0,pts:matchPoints(m)[id]||0,played:false};
  (m.inn||[]).forEach(inn=>{const st=innStats(inn);
    if(inn.bat===team&&st.bat[id]){r.bat=st.bat[id];r.notOut=!st.bat[id].out;r.played=true}
    if(inn.bat!==team&&st.bowl[id]){r.bowl=st.bowl[id];r.played=true}
    inn.balls.forEach(b=>{if(validW(b)&&b.w.f===id&&["c","st","ro"].includes(b.w.k)){r.ct++;r.played=true}if(b.s===id||b.ns===id)r.played=true});
  });
  const xi=m.xi?.[team];if(xi&&xi.includes(id)&&(m.inn||[]).length)r.played=true;
  return r;
}
function playerView(){
  const id=ui.playerId,team=pteam(id);if(!team)return statsView();
  const p=teamOf(team).players.find(x=>x.id===id);const me=tmeta(team);
  const{bat,bowl}=tourStats();const b=bat[id],w=bowl[id];
  const rows=Object.values(M).filter(m=>(m.a===team||m.b===team)&&(m.inn||[]).length).sort(byNo).map(m=>playerLine(m,id)).filter(r=>r.played);
  const mvpAll=mvpTable();const rank=mvpAll.findIndex(r=>r.id===id)+1;const me2=mvpAll.find(r=>r.id===id);
  const tile=(lab,val,sub)=>`<div class="ptile"><span class="lab">${lab}</span><b>${val}</b>${sub?`<span class="muted small">${sub}</span>`:""}</div>`;
  const stg=m=>isLeague(m)?"M"+m.no:m.stage;
  return`<section><button class="btn sm" data-act="pback">← Back</button>
  <div class="board" style="background:linear-gradient(160deg,${me.color} -40%,var(--board) 55%)"><div class="teamhero">${badge(team,84)}<div><div class="champ-name">${esc(p.name)}</div>
  <div class="small" style="color:var(--board-muted)"><span class="plink" data-act="team" data-id="${team}">${esc(me.name)}</span>${p.role?` · ${esc({Bat:"Batter",AR:"All-rounder",WK:"Wicket-keeper",Bowl:"Bowler"}[p.role]||p.role)}`:""}${p.age?` · ${p.age} yrs`:""}</div>
  ${me2?`<div class="rates"><span>MVP points <b>${me2.pts}</b></span><span>MVP rank <b>#${rank}</b></span><span>Matches <b>${rows.length}</b></span></div>`:""}</div></div></div>
  ${rows.length?`<div class="ptiles">${tile("Runs",b?.r||0,b?.b?`${b.b} balls · SR ${(b.r*100/b.b).toFixed(0)}`:"")}${tile("High score",b&&b.hs>=0?b.hs+(b.hsNo?"*":""):"–",b?`${b.f} fours · ${b.s} sixes`:"")}${tile("Wickets",w?.w||0,w?.l?`${ovs(w.l)} ov · Econ ${rate(w.r,w.l)}`:"")}${tile("Best bowling",w&&w.bw>=0?w.bw+"/"+w.br:"–",me2?`${me2.f} catches/run-outs`:"")}</div>
  <h2>Match by match</h2><div class="tbl"><table><thead><tr><th>Match</th><th>Bat</th><th>Bowl</th><th>Ct</th><th>Pts</th></tr></thead><tbody>${rows.map(r=>{const opp=r.m.a===team?r.m.b:r.m.a;
    return`<tr data-act="view" data-id="${r.m.id}" class="clk"><td class="n"><span class="tl">${badge(opp,22)}<span class="tn"><b>v ${esc(tmeta(opp).short)}</b><span class="how">${esc(stg(r.m))}${r.m.winner===team?" · won":r.m.winner&&r.m.winner!=="tie"&&r.m.winner!=="nr"&&r.m.status==="done"?" · lost":""}</span></span></span></td>
    <td>${r.bat?`<b>${r.bat.r}${r.notOut?"*":""}</b><span class="muted small"> (${r.bat.b})</span>`:`<span class="muted">–</span>`}</td><td>${r.bowl?`<b>${r.bowl.w}/${r.bowl.r}</b><span class="muted small"> (${ovs(r.bowl.l)})</span>`:`<span class="muted">–</span>`}</td><td>${r.ct||""}</td><td><b>${r.pts}</b></td></tr>`}).join("")}</tbody></table></div>
  <p class="kv">Tap a match to open its scorecard. Points use the fantasy/MVP scoring.</p>`
  :`<div class="empty"><strong>Yet to play</strong>Stats appear here after ${esc(p.name.split(" ")[0])}'s first match.</div>`}</section>`;
}

/* ================= rules & sponsors ================= */
function sponsorsBlock(){
  const L=CFG.sponsorList||[];const title=(CFG.welcome?.sponsors||[]).find(s=>s.logo);
  if(!L.length&&!title)return"";
  return`<h2>Our sponsors</h2><div class="spons">${title?`<div class="spg main"><span class="label">${esc(title.role||"Title sponsor")}</span><span class="wl-tile${title.dark?" dark":""}"><img src="brand/${esc(title.logo)}" alt="${esc(title.name||"")}"></span>${title.sub?`<b class="spsub">${esc(title.sub)}</b>`:""}</div>`:""}
  ${L.map(g=>{
    // Team sponsors are listed in team order with the team name on top; other groups keep their own order
    const TM=window.MASCON_TEAMS||[],KK=Object.keys(KSP);
    const rows=g.names.map(n=>{const ti=TM.findIndex(t=>t.sponsor&&t.sponsor.toLowerCase()===n.toLowerCase());const ki=KK.findIndex(k=>KSP[k].toLowerCase()===n.toLowerCase());
      return{n,team:ti>=0?TM[ti].name:ki>=0?KK[ki]:"",ord:ti>=0?ti:ki>=0?ki:999}});
    if(rows.some(r=>r.team))rows.sort((a,b)=>a.ord-b.ord);
    return`<div class="spg"><span class="label">${esc(g.title)}</span><div class="spn-list">${rows.map(r=>`<div class="spn">${r.team?`<em>${esc(r.team)}</em>`:""}<b>${esc(r.n)}</b></div>`).join("")}</div></div>`}).join("")}</div>`;
}
const RULES=[
 ["Format",["10 teams in 2 groups (A and B) of 5. Each team plays the other 4 in its group: 4 league matches each.","Group toppers go straight to the semi-finals. 2nd and 3rd play the quarter-finals: A2 v B3 and B2 v A3.","All matches, league and knockout, are 12 overs a side.","Win = 2 points. A league tie = 1 point each.","Teams level on points are split by net run rate (runs scored ÷ overs faced − runs conceded ÷ overs bowled). An all-out side counts the full 12 overs."]],
 ["Squads and timing",["Reporting time is 30 minutes before the match. Dark blue tracks, team jersey and sports shoes.","13 players per match; any 11 can bat and field. A player who leaves the field can bowl only after fielding for one over.","At least 9 players must be present at the toss, otherwise a walkover goes to the opponents.","Each team gets 50 minutes to bowl its overs. One over is cut for every 4 minutes of delay, applied when the late team bats.","The match can start any time, on any pitch, after reporting time."]],
 ["Bowling matrix",["12 overs: 2 bowlers × 3 overs + 3 bowlers × 2 overs.","10 overs: 5 bowlers × 2 overs.","8 overs: 3 bowlers × 2 overs + 2 bowlers × 1 over.","The wicket-keeper can also bowl."]],
 ["Powerplay and Mascon over",["Overs 1 and 2 are compulsory powerplay: at most 2 fielders outside the inner circle (with 11 players).","Over 7 is the Mascon Over (over 6 in a 10-over match): every fielder inside the 30-yard circle.","A different bowler must bowl each of these 3 special overs.","Ends change after 6 overs (5 in a 10-over match)."]],
 ["Playing rules",["Free hit on every no ball. On a free hit, the batter can only be run out.","No LBW and no leg byes. A batter out of the crease can still be run out.","If a batter switch-hits, both wide lines come into play and the bowler can bowl on either side within them."]],
 ["Ties and knockouts",["League tie: 1 point each.","Quarter-final, semi-final or final tie: a Super Over. Each team names 3 batters and 1 bowler; the side batting second bats first in the Super Over. Highest score wins."]],
 ["Bad light, rain or other delays",["Playing time cut by 30 min: 10 overs a side, same powerplay rules.","Cut by 45 min: 8 overs a side; only over 1 and the Mascon over are powerplay.","Cut by 60 min: 6 overs a side, no powerplay overs.","For a result, the side batting second must face at least half its overs. Its target is the first side's average × half the overs + 1. Otherwise, once a ball is bowled, 1 point each with 0 NRR.","Unplayed matches move to the next reserve day at any ground. Only players available on the original date can play on the rescheduled day."]],
 ["Injury",["The SAJYM ground committee and umpires decide whether an injured player gets a runner.","No runner for an injury from before the match."]],
 ["Conduct",["Sponsors and captains are requested to have every player field at least 6 overs in at least one match.","The umpire's decision is final. Only the captain may raise a dispute, calmly, with the umpires and organisers. Dissent or bad behaviour means a ban for the rest of the tournament.","The organisers may change any rule, including the overs per match, if required."]]
];
/* Fantasy league rules: shown on the Fantasy tab before picking, and on the Rules tab */
/* iPhone notice: Safari and the home-screen icon keep separate storage, so a team made in one does not show in the other */
function iosNoteHtml(){
  const ios=/iPhone|iPad|iPod/i.test(navigator.userAgent),standalone=matchMedia("(display-mode: standalone)").matches||navigator.standalone;
  const extra=ios&&standalone&&!FT.mine?`<p><b>Made your team in Safari?</b> Open the link in Safari to see it and make changes.</p>`:"";
  return`<div class="iosnote"><b>📱 iPhone users, please read</b><p>On iPhone, Safari and the home-screen icon save data separately. A fantasy team made in Safari will not show in the icon (and the other way round).</p><p><b>What to do:</b> open the link in Safari → tap Share ⬆ → <b>Add to Home Screen</b> → open the Mascon Cup icon and make your team there. Always use the icon after that.</p>${extra}<p class="small">Android phones are not affected.</p></div>`;
}
function fantasyRulesHtml(open){
  const li=a=>`<ul>${a.map(x=>`<li>${x}</li>`).join("")}</ul>`;
  return`<details class="card frules"${open?" open":""}><summary><span>Fantasy league rules</span></summary><div class="in">
  <h4>Your team: 13 players</h4>${li(["At least <em>3 batters or wicketkeepers</em>","At least <em>2 bowlers</em>","At least <em>3 all-rounders</em>","The other 5 can be any role","At most <em>3 players from one team</em>","At most <em>2 icon players</em>"])}
  <h4>Captain and vice-captain</h4>${li(["Your <em>captain</em> earns <em>2×</em> points","Your <em>vice-captain</em> earns <em>1.5×</em> points"])}
  <h4>Deadlines and substitutions</h4>${li(["Teams lock at the <em>first ball on 29 November</em>","<em>2 substitutions before match day 2</em> (6 Dec) and <em>2 more before match day 3</em> (13 Dec)","Substitutions open when the last match of the day ends and close at the first ball of the next match day","You can also change your captain and vice-captain in each window","Points a player has already earned for you stay on your team when you swap him out"])}
  <h4>Leaderboard</h4>${li(["Updates when each match ends","One team per phone"])}
  </div></details>`;
}
function rulesView(){
  return`<section><h2>Rules and regulations</h2>${KIDS?"":fantasyRulesHtml(false)}${KIDS?`<div class="panel"><b>Kids tournament</b><span class="kv">The kids' rules will be posted here. The adults' rules below are for reference.</span></div>`:""}${RULES.map(([h,l],i)=>`<details class="card"${i<2?" open":""}><summary><span>${esc(h)}</span></summary><div class="in"><ul class="rules">${l.map(x=>`<li>${esc(x)}</li>`).join("")}</ul></div></details>`).join("")}
  <div class="panel"><div class="label">For further details</div><div class="row-btns"><a class="btn sm" href="tel:+919844142007">Rahul Dantewadia · 98441 42007</a><a class="btn sm" href="tel:+919844026175">Kalpesh Sonwadia · 98440 26175</a></div></div>
  ${sponsorsBlock()}</section>`;
}

/* ================= result card image ================= */
function lightCol(h){const n=parseInt((h||"#888").slice(1),16);const r=n>>16&255,g=n>>8&255,b=n&255;return(0.299*r+0.587*g+0.114*b)<110?"#DDDDDD":h}
function loadImg(src){return new Promise(r=>{if(!src)return r(null);const i=new Image();i.onload=()=>r(i);i.onerror=()=>r(null);i.src=src})}
async function resultCard(m,btn){
  if(!m||!m.inn?.length)return;const old=btn?.textContent;if(btn){btn.disabled=true;btn.textContent="Making image…"}
  try{
    try{await Promise.all(['800 60px "Saira Condensed"','700 40px "Saira Condensed"','600 28px "Barlow"','500 28px "Barlow"'].map(f=>document.fonts.load(f)))}catch(e){}
    const W=1080,H=1350,c=document.createElement("canvas");c.width=W;c.height=H;const x=c.getContext("2d");
    const Y="#FFC72C",SC='"Saira Condensed",sans-serif',BR='"Barlow",sans-serif';
    const txt=(t,X,Yp,weight,size,col,align,max,fam)=>{let s=size;x.textAlign=align||"left";x.fillStyle=col;do{x.font=`${weight} ${s}px ${fam||SC}`;s-=2}while(max&&x.measureText(t).width>max&&s>14);x.fillText(t,X,Yp)};
    const rr=(X,Y0,w,h,r)=>{x.beginPath();x.moveTo(X+r,Y0);x.arcTo(X+w,Y0,X+w,Y0+h,r);x.arcTo(X+w,Y0+h,X,Y0+h,r);x.arcTo(X,Y0+h,X,Y0,r);x.arcTo(X,Y0,X+w,Y0,r);x.closePath()};
    const first=m.inn[0].bat,second=first===m.a?m.b:m.a;
    const [lg,ms,l1,l2]=await Promise.all([loadImg(CFG.appLogo?"brand/"+CFG.appLogo:""),loadImg("brand/mascon-dark.png"),loadImg(tmeta(first).logo),loadImg(tmeta(second).logo)]);
    x.fillStyle="#000";x.fillRect(0,0,W,H);x.fillStyle=Y;x.fillRect(0,0,W,14);
    if(lg)x.drawImage(lg,60,46,120,120);
    txt((T?.name||DEF.name).replace(/\s*\(DEMO\)/i,"").toUpperCase(),200,112,800,60,Y,"left",820);
    txt(`${stageLabel(m)}${m.when?" · "+fmtDay(m.when):""}`,202,154,600,30,"#ddd","left",820,BR);
    const win=m.winner&&m.winner!=="tie"&&m.winner!=="nr"?m.winner:null;
    [[first,0,l1],[second,1,l2]].forEach(([tid,i,logo])=>{
      const y0=210+i*240,mt=tmeta(tid);rr(50,y0,W-100,210,22);x.fillStyle="#141414";x.fill();
      if(win===tid){x.lineWidth=5;x.strokeStyle=Y;x.stroke()}
      x.fillStyle=mt.color;x.fillRect(50,y0+22,10,166);
      if(logo){x.save();x.beginPath();x.arc(165,y0+105,78,0,Math.PI*2);x.clip();x.drawImage(logo,87,y0+27,156,156);x.restore()}
      const inn=m.inn.find(q=>q.bat===tid);const st=inn?innStats(inn):null;
      txt(mt.name.toUpperCase(),270,y0+92,700,46,"#fff","left",400);
      if(mt.sponsor)txt(mt.sponsor,272,y0+130,500,24,"#aaa","left",400,BR);if(win===tid)txt("WINNER",272,y0+(mt.sponsor?170:136),600,26,Y,"left",0,BR);
      if(st){txt(`${st.runs}/${st.wk}`,W-90,y0+128,800,110,win===tid?Y:"#fff","right");txt(`${ovs(st.legal)} overs`,W-92,y0+172,500,28,"#aaa","right",0,BR)}
      else txt("Did not bat",W-90,y0+120,600,34,"#aaa","right",0,BR);
    });
    x.fillStyle=Y;x.fillRect(0,700,W,104);txt(m.result||"",W/2,768,800,50,"#000","center",W-100);
    const mv=matchMvp(m);let yy=880;
    if(mv){const r=playerLine(m,mv.id);const f=[r.bat?`${r.bat.r}${r.notOut?"*":""} (${r.bat.b})`:"",r.bowl?`${r.bowl.w}/${r.bowl.r} (${ovs(r.bowl.l)} ov)`:"",r.ct?`${r.ct} ct/ro`:""].filter(Boolean).join("  ·  ");
      txt("PLAYER OF THE MATCH",W/2,yy,600,28,"#aaa","center",0,BR);txt(pname(mv.id).toUpperCase(),W/2,yy+72,800,78,"#fff","center",W-120);
      txt(`${tmeta(pteam(mv.id)).name}${f?"  ·  "+f:""}`,W/2,yy+118,500,30,Y,"center",W-120,BR);yy+=170}
    // top performers per side
    const tops=tid=>{const bi=m.inn.find(q=>q.bat===tid),oi=m.inn.find(q=>q.bat!==tid);const out=[];
      if(bi){const s=innStats(bi);const b=s.batOrder.map(id=>[id,s.bat[id]]).sort((a,c)=>c[1].r-a[1].r||a[1].b-c[1].b)[0];if(b)out.push(`${pname(b[0])} ${b[1].r}${b[1].out?"":"*"} (${b[1].b})`)}
      if(oi){const s=innStats(oi);const b=s.bowlOrder.map(id=>[id,s.bowl[id]]).sort((a,c)=>c[1].w-a[1].w||a[1].r-c[1].r)[0];if(b)out.push(`${pname(b[0])} ${b[1].w}/${b[1].r}`)}return out};
    x.strokeStyle="#333";x.lineWidth=2;x.beginPath();x.moveTo(80,yy);x.lineTo(W-80,yy);x.stroke();
    [[first,80,"left"],[second,W-80,"right"]].forEach(([tid,X,al])=>{txt(tmeta(tid).short.toUpperCase(),X,yy+48,700,34,lightCol(tmeta(tid).color),al,440);tops(tid).forEach((t,i)=>txt(t,X,yy+92+i*40,500,28,"#ddd",al,440,BR))});
    x.fillStyle="#000";x.fillRect(0,H-130,W,130);x.fillStyle=Y;x.fillRect(0,H-130,W,4);
    if(ms){const h=74,w=ms.width*h/ms.height;x.drawImage(ms,60,H-104,w,h)}
    txt("Live scores",W-60,H-74,600,26,"#aaa","right",0,BR);txt((location.host||"ahore-mascon-cup.netlify.app"),W-60,H-38,700,32,Y,"right",520);
    const blob=await new Promise(r=>c.toBlob(r,"image/png"));
    const name=`${tmeta(first).short}-v-${tmeta(second).short}-${stageLabel(m)}`.replace(/[^\w-]+/g,"-")+".png";
    const file=new File([blob],name,{type:"image/png"});
    if(navigator.canShare&&navigator.canShare({files:[file]})){try{await navigator.share({files:[file]})}catch(e){}}
    else{const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download=name;document.body.appendChild(a);a.click();a.remove();setTimeout(()=>URL.revokeObjectURL(a.href),4000)}
  }catch(e){console.error(e);flash("Couldn't make the image on this phone.")}
  finally{if(btn){btn.disabled=false;btn.textContent=old}}
}
function loginView(){
  if(canScore){ui.tab="score";return scoreView()}
  return`<section><div class="panel"><h2>Scorer login</h2><p class="kv">Enter the scorer PIN given by the organisers.</p>
  <form id="login-form" class="row-btns" style="align-items:stretch"><input id="pin" type="password" inputmode="numeric" autocomplete="current-password" placeholder="Scorer PIN" style="flex:1;min-width:140px"><button class="btn pri" type="submit"${ui.busyLogin?" disabled":""}>${ui.busyLogin?"Checking…":"Log in"}</button></form>
  ${ui.loginErr?`<div class="msg" style="color:var(--out)">${esc(ui.loginErr)}</div>`:""}</div></section>`;
}

/* ================= scorer ================= */
function confirmHtml(){return pendingConfirm?`<div class="confirm"><div>${esc(pendingConfirm.msg)}</div><div class="row-btns"><button class="btn warn" data-act="confirmYes">${esc(pendingConfirm.yes)}</button><button class="btn" data-act="confirmNo">Cancel</button></div></div>`:""}
function ask(msg,yes,fn){pendingConfirm={msg,yes,fn};render()}
function selectHtml(id,items,label,sel){
  return`<div class="field"><label class="label" for="${id}">${label}</label><select id="${id}">${items.map(p=>`<option value="${p.id}"${p.disabled?" disabled":""}${p.id===sel?" selected":""}>${esc(p.name)}${p.why?" — "+esc(p.why):""}</option>`).join("")}</select></div>`;
}
function scoreView(){
  if(!T)return`<section><div class="empty"><strong>Set up the tournament first</strong>Add the teams, groups and squads in Setup.</div><button class="btn pri" data-act="tab" data-v="setup">Open Setup</button></section>`;
  const list=Object.values(M).sort(byNo);
  const active=list.filter(m=>LIVE.includes(m.status));
  const next=list.filter(m=>m.status==="scheduled").slice(0,6);
  const sel=M[ui.scoreSel];
  let body;
  if(ui.scoreSel==="new")body=newMatchHtml();
  else if(sel)body=padHtml(sel);
  else body=`<div class="empty"><strong>Pick a match to score</strong>Upcoming fixtures are listed above. Knockout matches are added with New match.</div>`;
  const b=m=>`<button class="btn sm${ui.scoreSel===m.id?" pri":""}" data-act="ssel" data-id="${m.id}">${isLeague(m)?"M"+m.no:esc(m.stage)}: ${esc(tname(m.a))} v ${esc(tname(m.b))}</button>`;
  return`<section>${confirmHtml()}
  ${active.length?`<div class="label">In progress</div><div class="row-btns">${active.map(b).join("")}</div>`:""}
  ${next.length?`<div class="label">Next up</div><div class="row-btns">${next.map(b).join("")}</div>`:""}
  <div class="row-btns"><button class="btn sm${ui.scoreSel==="new"?" pri":""}" data-act="newMatch">+ New match</button>${list.some(m=>m.status==="done")?`<select id="done-sel" data-donesel="1" aria-label="Completed matches" style="width:auto;flex:1;min-width:160px"><option value="">Completed matches…</option>${list.filter(m=>m.status==="done").map(m=>`<option value="${m.id}"${ui.scoreSel===m.id?" selected":""}>${isLeague(m)?"M"+m.no:esc(m.stage)}: ${esc(tmeta(m.a).short)} v ${esc(tmeta(m.b).short)}</option>`).join("")}</select>`:""}</div>
  ${body}</section>`;
}
function suggest(stage){
  const a=pointsTable("A"),b=pointsTable("B");
  if(stage==="QF1")return[a[1]?.id,b[2]?.id];
  if(stage==="QF2")return[b[1]?.id,a[2]?.id];
  if(stage==="SF1")return[a[0]?.id,null];
  if(stage==="SF2")return[b[0]?.id,null];
  return[null,null];
}
function newMatchHtml(){
  const teams=T.teams;if(teams.length<2)return`<div class="empty"><strong>Need two teams</strong>Add teams in Setup.</div>`;
  const nm=ui.nm||(ui.nm={stage:"QF1",a:teams[0].id,b:teams[1].id});
  const opt=sel=>teams.map(t=>`<option value="${t.id}"${t.id===sel?" selected":""}>${esc(t.name)} (Grp ${t.group})</option>`).join("");
  return`<div class="panel"><h2>New match</h2>
  <div class="field"><label class="label" for="nm-stage">Stage</label><select id="nm-stage" data-nm="stage">${Object.entries(STAGES).map(([k,l])=>`<option value="${k}"${nm.stage===k?" selected":""}>${l}</option>`).join("")}</select></div>
  <div class="grid2"><div class="field"><label class="label" for="nm-a">Team 1</label><select id="nm-a" data-nm="a">${opt(nm.a)}</select></div>
  <div class="field"><label class="label" for="nm-b">Team 2</label><select id="nm-b" data-nm="b">${opt(nm.b)}</select></div></div>
  ${nm.stage.startsWith("QF")?`<p class="kv">Teams are filled in from the current group tables. Change them if needed.</p>`:""}
  ${nm.a===nm.b?`<div class="msg" style="color:var(--out)">Pick two different teams.</div>`:""}
  <button class="btn pri" data-act="createMatch"${nm.a===nm.b?" disabled":""}>Add match</button></div>`;
}
function tossHtml(m){
  const tz=ui.toss&&ui.toss.id===m.id?ui.toss:(ui.toss={id:m.id,toss:m.a,chose:"bat",xi:{[m.a]:xiOf(m,m.a),[m.b]:xiOf(m,m.b)},overs:mOvers(m)});
  const xiBox=team=>{const sq=teamOf(team)?.players||[],chosen=new Set(tz.xi[team]),n=tz.xi[team].length;
    return`<div class="label">${esc(tname(team))} playing XI · ${n} picked</div><div class="xi">${sq.map(p=>`<label><input type="checkbox" data-xi="${team}:${p.id}"${chosen.has(p.id)?" checked":""}>${esc(p.name)}</label>`).join("")}</div>`};
  const bad=[tz.xi[m.a].length,tz.xi[m.b].length].some(n=>n<T.minXi||n>T.xi);
  return`<div class="panel"><h2>Toss and playing XI</h2>
  <div class="grid2"><div class="field"><label class="label" for="tz-toss">Toss won by</label><select id="tz-toss" data-tz="toss"><option value="${m.a}"${tz.toss===m.a?" selected":""}>${esc(tname(m.a))}</option><option value="${m.b}"${tz.toss===m.b?" selected":""}>${esc(tname(m.b))}</option></select></div>
  <div class="field"><label class="label" for="tz-chose">Chose to</label><select id="tz-chose" data-tz="chose"><option value="bat"${tz.chose==="bat"?" selected":""}>Bat</option><option value="bowl"${tz.chose==="bowl"?" selected":""}>Bowl</option></select></div>
  <div class="field"><label class="label" for="tz-overs">Overs per side</label><select id="tz-overs" data-tz="overs">${[12,10,8,6].map(o=>`<option value="${o}"${+tz.overs===o?" selected":""}>${o}</option>`).join("")}</select></div></div>
  ${xiBox(m.a)}${xiBox(m.b)}
  ${bad?`<div class="msg" style="color:var(--out)">Each side needs ${T.minXi} to ${T.xi} players at the toss. Fewer than ${T.minXi} is a walkover (see Match settings below).</div>`:""}
  <button class="btn pri" data-act="tossDone"${bad?" disabled":""}>Save toss</button></div>`;
}
function openersHtml(m){
  const second=m.inn.length===1;
  const bat=second?m.inn[0].bowl:batFirst(m),bowl=bat===m.a?m.b:m.a;
  const bp=xiPlayers(m,bat),wp=xiPlayers(m,bowl);
  const chaseT=second?(m.tgt||innStats(m.inn[0]).runs+1):0;
  return`<div class="panel"><h2>${second?"Second innings":"Openers"}</h2>
  <p class="kv"><b>${esc(tname(bat))}</b> bat${second?`, chasing ${chaseT}`:""}. <b>${esc(tname(bowl))}</b> bowl.</p>
  <div class="grid2">${selectHtml("op-s",bp,"Striker",bp[0]?.id)}${selectHtml("op-ns",bp,"Non-striker",bp[1]?.id)}</div>
  ${selectHtml("op-bw",wp,"Bowler for over 1 (powerplay)")}
  <button class="btn pri" data-act="startInn" data-bat="${bat}" data-bowl="${bowl}">Start innings</button></div>`;
}
function otherResultHtml(m){
  return`<details class="card"><summary><span>Match settings</span><span class="muted small">overs, revised target, no result, walkover</span></summary><div class="in">
  <div class="grid2"><div class="field"><label class="label" for="ms-overs">Overs per side</label><select id="ms-overs">${[12,10,8,6].map(o=>`<option${mOvers(m)===o?" selected":""}>${o}</option>`).join("")}</select></div>
  ${m.inn.length>1||m.status==="break"?`<div class="field"><label class="label" for="ms-ov2">2nd innings overs</label><select id="ms-ov2"><option value="">Same</option>${[12,11,10,9,8,7,6,5,4,3].map(o=>`<option${m.ov2===o?" selected":""}>${o}</option>`).join("")}</select></div>
  <div class="field"><label class="label" for="ms-tgt">Revised target</label><input id="ms-tgt" type="number" inputmode="numeric" min="1" value="${m.tgt||""}" placeholder="Auto"></div>`:""}</div>
  <button class="btn sm" data-act="saveSettings">Apply</button>
  <div class="label">End the match another way</div>
  <div class="row-btns"><button class="btn sm" data-act="noResult">No result (1 pt each)</button><button class="btn sm" data-act="walkover" data-w="${m.a}">Walkover to ${esc(tname(m.a))}</button><button class="btn sm" data-act="walkover" data-w="${m.b}">Walkover to ${esc(tname(m.b))}</button></div>
  <button class="btn sm warn" data-act="delMatch">Delete this match</button></div></details>`;
}
function badBallsBanner(m){const n=m.inn.reduce((a,i)=>a+i.balls.filter(invalidW).length,0);
  return n?`<div class="confirm"><div><b>${n} wicket${n>1?"s":""} recorded against the rules</b> (for example caught off a no ball). They are not counted. Open <b>Fix an earlier ball</b>, tap the red ball and set it right; check who is at the crease afterwards.</div><button class="btn sm" data-act="sheet" data-k="fix">Fix now</button></div>`:""}
function padHtml(m){
  const head=badBallsBanner(m)+`<div class="row-btns" style="justify-content:space-between;align-items:center"><span class="label">${esc(stageLabel(m))}</span><button class="btn sm" data-act="view" data-id="${m.id}">Audience view</button></div>`;
  if(m.status==="scheduled")return head+boardHtml(m)+tossHtml(m)+otherResultHtml(m);
  if(m.status==="setup"||m.status==="break")return head+boardHtml(m)+sheetHtml(m)+openersHtml(m)+(m.status==="break"?`<div class="row-btns"><button class="btn" data-act="undo">Undo last ball of 1st innings</button><button class="btn" data-act="sheet" data-k="fix">Fix an earlier ball</button></div>`:`<button class="btn" data-act="redoToss">Redo toss</button>`)+otherResultHtml(m);
  if(m.status==="super")return head+boardHtml(m)+`<div class="panel"><h2>Super Over result</h2><p class="kv">Each side nominates 3 batters and 1 bowler. The team batting second bats first.</p>
    <div class="field"><label class="label" for="so-score">Super Over scores (shown to everyone)</label><input id="so-score" placeholder="e.g. ${esc(tname(m.inn[1].bat))} 11/1, ${esc(tname(m.inn[0].bat))} 9/2"></div>
    <div class="row-btns"><button class="btn pri" data-act="superWin" data-w="${m.a}">${esc(tname(m.a))} won</button><button class="btn pri" data-act="superWin" data-w="${m.b}">${esc(tname(m.b))} won</button></div><button class="btn" data-act="undo">Undo last ball</button></div>`;
  if(m.status==="done")return head+boardHtml(m)+sheetHtml(m)+`<div class="row-btns"><button class="btn" data-act="undo">Undo and reopen</button><button class="btn" data-act="sheet" data-k="fix">Fix an earlier ball</button></div>`;
  const i=m.inn.length-1,inn=m.inn[i],c=inn.cur,avail=availBatters(m,inn);
  let need="";
  if(c.s==null||(c.ns==null&&avail.length)){
    const slot=c.s==null?"s":"ns";
    need=`<div class="panel"><h2>Next batter</h2>${selectHtml("nb-sel",avail,slot==="s"?"New batter (on strike)":"New batter (non-striker)")}<button class="btn pri" data-act="pickBat" data-slot="${slot}">Send in</button><button class="btn" data-act="undo">Undo last ball</button></div>`;
  }else if(c.bw==null){
    const st=innStats(inn),n=Math.floor(st.legal/6)+1,tag=overTag(ovFor(m,i),n),mx=matrix(ovFor(m,i));
    const opts=bowlerOptions(m,i),firstOk=opts.find(o=>!o.disabled&&!o.why)||opts.find(o=>!o.disabled);
    need=`<div class="panel"><h2>Bowler for over ${n}${tag?" · "+tag:""}</h2>${selectHtml("bw-sel",opts,"Bowler",firstOk?.id)}<p class="kv">For ${ovFor(m,i)} overs: no bowler above ${mx.max} overs, and only ${mx.atMax} may bowl ${mx.max}. Each powerplay and Mascon over needs a different bowler. Breaks are flagged, not blocked.</p><button class="btn pri" data-act="pickBowl">Start over</button><button class="btn" data-act="undo">Undo last ball</button></div>`;
  }
  if(need)return head+boardHtml(m)+need+otherResultHtml(m);
  return head+boardHtml(m)+sheetHtml(m)+`<div class="pad">
  ${[0,1,2,3].map(r=>`<button class="k" data-act="run" data-r="${r}">${r}</button>`).join("")}
  <button class="k r4" data-act="run" data-r="4">4</button><button class="k r6" data-act="run" data-r="6">6</button>
  <button class="k ex" data-act="sheet" data-k="wd">Wide</button><button class="k ex" data-act="sheet" data-k="nb">No ball</button>
  <button class="k ex" data-act="sheet" data-k="bye">Bye</button>${T.noLegBye?`<button class="k tool" data-act="run" data-r="5">5</button>`:`<button class="k ex" data-act="sheet" data-k="lb">Leg bye</button>`}
  <button class="k wk" data-act="sheet" data-k="w">OUT</button>
  <button class="k tool" data-act="undo">Undo</button><button class="k tool" data-act="swap"${c.ns?"":" disabled"}>Swap strike</button>
  <button class="k tool" data-act="changeBowler">Change bowler</button><button class="k tool" data-act="endInn">End innings</button><button class="k tool" data-act="sheet" data-k="fix" style="grid-column:span 2">Fix an earlier ball</button></div>`+otherResultHtml(m);
}
function fixSheet(m,s,close){
  const ii=s.ii??m.inn.length-1,inn=m.inn[ii];if(!inn||!inn.balls.length)return`<div class="sheet"><div class="label">Fix an earlier ball</div><p class="kv">No balls bowled yet.</p>${close}</div>`;
  const st=innStats(inn);
  if(s.idx==null){
    const rows=st.log.slice(-18).reverse();
    return`<div class="sheet"><div class="label">Fix an earlier ball · tap the ball</div>${m.inn.length>1?`<div class="opts">${m.inn.map((x,i)=>`<button class="opt" data-act="fixInn" data-v="${i}" aria-pressed="${i===ii}">${esc(tmeta(x.bat).short)} innings</button>`).join("")}</div>`:""}
    <div class="feed">${rows.map(e=>{const idx=inn.balls.indexOf(e.b);return`<button class="row fixrow${invalidW(e.b)?" badrow":""}" data-act="fixPick" data-v="${idx}"><span class="ov">${e.lab}</span>${chip(e.b)}<span class="txt">${feedText(e.b)}</span></button>`}).join("")}</div>${close}</div>`;
  }
  const b=inn.balls[s.idx],d=s.d;const bp=xiPlayers(m,inn.bat),wp=xiPlayers(m,inn.bowl);
  const sel=(id,items,lab,v,blank)=>`<div class="field"><label class="label" for="${id}">${lab}</label><select id="${id}" data-fix="${id.slice(3)}">${blank?`<option value="">—</option>`:""}${items.map(p=>`<option value="${p.id}"${p.id===v?" selected":""}>${esc(p.name)}</option>`).join("")}</select></div>`;
  return`<div class="sheet"><div class="label">Fixing ball ${st.log[s.idx].lab} · ${esc(pname(b.bw))} to ${esc(pname(b.s))}</div>
  <div class="grid2">${sel("fx-s",bp,"Striker",d.s)}${sel("fx-ns",bp,"Non-striker",d.ns)}</div>
  <label class="check"><input type="checkbox" data-fix="batLater"${d.batLater?" checked":""}> Also apply the batter change to every later ball this innings (use when the wrong batter was picked)</label>
  ${sel("fx-bw",wp,"Bowler",d.bw)}
  <label class="check"><input type="checkbox" data-fix="bwOver"${d.bwOver?" checked":""}> Apply the bowler change to the whole over</label>
  <div class="grid2"><div class="field"><label class="label" for="fx-t">Delivery</label><select id="fx-t" data-fix="t">${[["run","Legal"],["wd","Wide"],["nb","No ball"],["bye","Bye"]].map(([v,l])=>`<option value="${v}"${d.t===v?" selected":""}>${l}</option>`).join("")}</select></div>
  <div class="field"><label class="label" for="fx-r">Runs</label><select id="fx-r" data-fix="r">${[0,1,2,3,4,5,6].map(r=>`<option${d.r===r?" selected":""}>${r}</option>`).join("")}</select></div></div>
  ${(()=>{const prev=inn.balls[s.idx-1];const fh=T.freeHit&&prev&&(prev.t==="nb"||(prev.fh&&prev.t==="wd"));const allowed=d.t==="nb"||fh?["ro"]:d.t==="wd"?["ro","st"]:null;
    const kinds=KINDS.filter(k=>!(T.noLbw&&k[0]==="lbw")).filter(k=>!allowed||allowed.includes(k[0]));
    return`<div class="field"><label class="label" for="fx-wk">Wicket${allowed?` <span class="muted">(${d.t==="nb"?"no ball":fh?"free hit":"wide"}: ${allowed.map(x=>KINDS.find(k=>k[0]===x)[1].toLowerCase()).join(" or ")} only)</span>`:""}</label><select id="fx-wk" data-fix="wk"><option value="">No wicket</option>${kinds.map(([k,l])=>`<option value="${k}"${d.wk===k?" selected":""}>${l}</option>`).join("")}</select></div>`})()}
  ${d.wk?`<div class="grid2">${sel("fx-out",bp,"Who is out",d.out)}${sel("fx-f",wp,"Fielder",d.f,true)}</div>`:""}
  <p class="kv">Totals, scorecards and fantasy points recalculate from the balls, so this fixes everything downstream.</p>
  <div class="row-btns"><button class="btn pri" data-act="fixSave">Save fix</button><button class="btn" data-act="fixBack">Back to list</button>${close}</div></div>`;
}
function sheetHtml(m){
  const s=ui.sheet;if(!s)return"";
  const close=`<button class="btn sm" data-act="closeSheet">Cancel</button>`;
  if(s.k==="fix")return fixSheet(m,s,close);
  const inn=last(m.inn),c=inn.cur,fh=isFreeHit(inn);
  if(s.k==="wd")return`<div class="sheet"><div class="label">Wide · runs taken besides the wide</div><div class="opts">${[0,1,2,3,4].map(r=>`<button class="opt" data-act="ext" data-r="${r}">${r===0?"Wide only":"+"+r}</button>`).join("")}</div>${close}</div>`;
  if(s.k==="nb")return`<div class="sheet"><div class="label">No ball · runs off the bat (next ball is a free hit)</div><div class="opts">${[0,1,2,3,4,6].map(r=>`<button class="opt" data-act="ext" data-r="${r}">${r===0?"No ball only":"+"+r}</button>`).join("")}</div>${close}</div>`;
  if(s.k==="bye"||s.k==="lb")return`<div class="sheet"><div class="label">${s.k==="bye"?"Byes":"Leg byes"}</div><div class="opts">${[1,2,3,4].map(r=>`<button class="opt" data-act="ext" data-r="${r}">${r}</button>`).join("")}</div>${close}</div>`;
  let kinds=KINDS.filter(k=>!(T.noLbw&&k[0]==="lbw"));if(fh)kinds=kinds.filter(k=>k[0]==="ro");
  const fielders=xiPlayers(m,inn.bowl);
  let more="";
  if(s.kind){
    if(["c","ro","st"].includes(s.kind))more+=`<div class="field"><label class="label" for="wk-f">${s.kind==="c"?"Caught by":s.kind==="st"?"Stumped by":"Fielder (optional)"}</label><select id="wk-f"><option value="">—</option>${fielders.map(p=>`<option value="${p.id}"${s.f===p.id?" selected":""}>${esc(p.name)}</option>`).join("")}</select></div>`;
    if(s.kind==="ro"){
      more+=`<div class="label">Who is out</div><div class="opts"><button class="opt" data-act="wo" data-v="s" aria-pressed="${s.out==="s"}">${esc(pname(c.s))} (striker)</button>${c.ns?`<button class="opt" data-act="wo" data-v="ns" aria-pressed="${s.out==="ns"}">${esc(pname(c.ns))}</button>`:""}</div>
      <div class="label">Runs completed</div><div class="opts">${[0,1,2,3].map(r=>`<button class="opt" data-act="wr" data-v="${r}" aria-pressed="${s.runs===r}">${r}</button>`).join("")}</div>`;
    }
    if(s.kind==="ro"||s.kind==="st"){
      const types=s.kind==="ro"?[["run","Legal ball"],["wd","Wide"],["nb","No ball"]]:[["run","Legal ball"],["wd","Wide"]];
      more+=`<div class="label">Delivery</div><div class="opts">${types.map(([v,l])=>`<button class="opt" data-act="wt" data-v="${v}" aria-pressed="${s.wt===v}">${l}</button>`).join("")}</div>`;
    }
    more+=`<button class="btn pri" data-act="wkConfirm">Confirm wicket</button>`;
  }
  return`<div class="sheet"><div class="label">How out${fh?" · free hit: run out only":""}</div><div class="opts">${kinds.map(([k,l])=>`<button class="opt" data-act="wk" data-v="${k}" aria-pressed="${s.kind===k}">${l}</button>`).join("")}</div>${more}${close}</div>`;
}

/* ================= setup ================= */
function poolPlayer(name){const p=POOL.find(x=>x.name.toLowerCase()===name.toLowerCase());return p?{id:uidGen("p"),name:p.name,reg:p.reg,role:p.role,age:p.age}:{id:uidGen("p"),name}}
function blankTeams(){
  if(PRESET.length)return PRESET.map(t=>({id:uidGen("t"),name:t.name,group:t.group,players:[poolPlayer(t.icon)]}));
  const t=[];for(const g of["A","B"])for(let i=1;i<=5;i++)t.push({id:uidGen("t"),name:"",group:g,players:Array.from({length:DEF.squad},()=>({id:uidGen("p"),name:""}))});return t}
function poolPanel(d){
  if(!POOL.length)return"";
  const q=(ui.poolQ||"").trim().toLowerCase();
  const owner={};d.teams.forEach(t=>t.players.forEach(p=>{if(p.reg)owner[p.reg]=t.id;else if(p.name){const m=POOL.find(x=>x.name.toLowerCase()===p.name.trim().toLowerCase());if(m&&!owner[m.reg])owner[m.reg]=t.id}}));
  const count=t=>t.players.filter(p=>p.name.trim()).length;
  const list=POOL.filter(p=>!q||p.name.toLowerCase().includes(q)||String(p.reg)===q);
  const show=ui.poolAll?list:list.filter(p=>!owner[p.reg]);
  const opts=tid=>`<option value="">— unsold —</option>`+d.teams.filter(t=>t.name.trim()).map(t=>`<option value="${t.id}"${t.id===tid?" selected":""}>${esc(t.name)} (${count(t)})</option>`).join("");
  const sold=Object.keys(owner).length;
  return`<details class="card"${sold<POOL.length&&T&&!squadsReadyFlag()?" open":""}><summary><span>Auction pool</span><span class="muted small">${sold} of ${POOL.length} assigned</span></summary><div class="in"><p class="kv">${sold} of ${POOL.length} players assigned. Pick a team next to each player as they're sold, then <b>Save teams</b> at the bottom. Nothing is shared until you save.</p>
  <div class="row-btns"><input id="pool-q" placeholder="Search name or reg no." value="${esc(ui.poolQ||"")}" data-poolq="1" style="flex:1;min-width:160px"><label class="check"><input type="checkbox" id="pool-all" data-poolall="1"${ui.poolAll?" checked":""}> Show sold too</label></div>
  <div class="pool">${show.map(p=>`<div class="prow pr"><span class="pn"><b>${esc(p.name)}</b> <span class="muted small">#${p.reg} · ${p.role}${p.avail!=="All"?" · "+esc(p.avail)+" only":""}</span></span><select data-pool="${p.reg}" aria-label="Team for ${esc(p.name)}">${opts(owner[p.reg])}</select></div>`).join("")||`<div class="kv">No players match.</div>`}</div></div></details>`;
}
function squadsReadyFlag(){return!!T&&T.teams.length>=2&&T.teams.every(t=>t.players.length>=DEF.minXi)}
function setupView(){
  const d=ui.draft||(ui.draft=T?clone(T):{...clone(DEF),teams:blankTeams()});
  const used=new Set(Object.values(M).flatMap(m=>[m.a,m.b]));
  const league=Object.values(M).filter(isLeague);
  const team=(t,idx)=>{const n=t.players.filter(p=>p.name.trim()).length;
    return`<details class="team"><summary><span>${esc(t.name||"Team "+(idx+1))}</span><span class="muted small">Group ${t.group} · ${n} players</span></summary><div class="in">
    <div class="prow"><input id="tn-${t.id}" value="${esc(t.name)}" placeholder="Team name" data-tname="${t.id}" aria-label="Team name"><select id="tg-${t.id}" data-tgroup="${t.id}" aria-label="Group"><option${t.group==="A"?" selected":""}>A</option><option${t.group==="B"?" selected":""}>B</option></select></div>
    ${t.players.map((p,i)=>`<div class="prow"><input id="pn-${p.id}" value="${esc(p.name)}" placeholder="Player ${i+1}${i===0?" (icon)":i===1?" (marquee)":""}" data-pname="${t.id}:${p.id}" aria-label="Player ${i+1}"><button class="btn sm" data-act="delPlayer" data-id="${t.id}:${p.id}" aria-label="Remove player">✕</button></div>`).join("")}
    <div class="row-btns"><button class="btn sm" data-act="addPlayer" data-id="${t.id}">+ Add player</button><button class="btn sm warn" data-act="delTeam" data-id="${t.id}"${used.has(t.id)?" disabled":""}>Remove team</button></div></div></details>`};
  const squadsReady=T&&T.teams.length>=2&&T.teams.every(t=>t.players.length>=DEF.minXi);
  const hasFixtures=league.length>0;
  return`<section>${confirmHtml()}
  ${KIDS?`<div class="panel"><h2>Kids tournament</h2><p class="kv">This is the separate kids section. Nothing here touches the adults' tournament. Set the overs and rules under Tournament, name the teams and add players under Teams and squads, save, then create the fixtures.</p><div id="qs-msg"></div></div>`:`<div class="panel"><h2>Tournament data</h2><p class="kv">The real tournament is set up. The demo, reset and set-up buttons have been removed so one wrong tap can't wipe live data. If a reset is ever needed, ask Sayyam.</p><div id="qs-msg"></div></div>`}
  <div class="panel"><h2>Tournament</h2>
  <div class="field"><label class="label" for="st-name">Name</label><input id="st-name" value="${esc(d.name)}" data-bind="name"></div>
  <div class="grid2">
   <div class="field"><label class="label" for="st-wideRuns">Runs for a wide</label><input id="st-wideRuns" type="number" min="0" max="2" value="${d.wideRuns}" data-bind="wideRuns"></div>
   <div class="field"><label class="label" for="st-nbRuns">Runs for a no ball</label><input id="st-nbRuns" type="number" min="0" max="2" value="${d.nbRuns}" data-bind="nbRuns"></div></div>
  ${KIDS?`<p class="kv">Kids: set the overs for each match at the toss (the scorer picks overs there). Bowling limits follow the adults' matrix for that many overs; tell the organisers if the kids' rules differ.</p>`:`<p class="kv">From the rules sheet: 12 overs a side, 11 play from a 13-player squad (minimum 9 at the toss), free hit on every no ball, no LBW, no leg byes, win 2 pts, tie or no result 1 pt each, Super Over for knockout ties.</p>`}</div>
  ${poolPanel(d)}
  <details class="card"><summary><span>Import teams and squads from text</span><span class="muted small">paste a list</span></summary><div class="in">
  <p class="kv">Paste one block per team: a line starting <b>Team</b>, then <b>Icon</b>, then player names one per line. Group is set by the order (first five = A). Players added to a team already in the list are merged by name.</p>
  <textarea id="imp-text" rows="8" placeholder="Team : Mobius Mavericks&#10;Icon : Sayyam Gadiya&#10;Player two&#10;Player three&#10;&#10;Team : Paramount Pioneers&#10;Icon : Deepak Dugar"></textarea>
  <button class="btn" data-act="importTeams">Import into form</button><div id="imp-msg"></div></div></details>
  <div class="panel"><h2>Teams and squads</h2><p class="kv">Five teams per group. Use the group dropdown to move a team.</p>
  ${["A","B"].map(g=>`<h3>Group ${g}</h3>`+d.teams.map((t,i)=>t.group===g?team(t,i):"").join("")).join("")}
  <button class="btn sm" data-act="addTeam">+ Add team</button></div>
  <div id="setup-msg"></div>
  <div class="row-btns"><button class="btn pri" data-act="saveSetup">Save teams</button>${T&&!league.length?`<button class="btn" data-act="fixtures">Create league fixtures</button>`:""}</div>
  ${schedulePanel()}
  <div class="panel"><h2>Leaderboards</h2><p class="kv">Fantasy and prediction tables update automatically when each match ends. Use this if a table looks out of date.</p>
  <div class="row-btns"><button class="btn" data-act="pubBoard">Update leaderboards now</button></div></div>
  ${KIDS?"":`<div class="panel"><h2>Fantasy substitutions</h2><p class="kv">Windows open automatically when the last match of a match day ends (fixtures need dates) and close at the next first ball. Now: <b>${SUBS.open?`window open for match day ${SUBS.phase+1}`:SUBS.phase>=2?"both windows used":`closed${SUBS.phase?` (window ${SUBS.phase} done)`:""}`}</b>.</p>
  <div class="row-btns">${!SUBS.open&&SUBS.phase<2?`<button class="btn" data-act="subsOpen">Open window for match day ${SUBS.phase+2}</button>`:""}${SUBS.open?`<button class="btn" data-act="subsClose">Close window</button>`:""}</div></div>`}
  <div class="panel"><h2>Backup on this phone</h2><p class="kv">Backups also run automatically online. This saves a copy of all teams and matches (every ball) to this phone as a file. Tap it at the end of each match day.</p>
  <div class="row-btns"><button class="btn" data-act="dlBackup">Download backup file</button></div></div>
  <div class="panel"><h2>Scorer PIN</h2><p class="kv">Anyone with the PIN can score. Change it after the tournament or if it leaks; other phones are logged out within an hour.</p>
  <div class="grid2"><div class="field"><label class="label" for="pin-cur">Current PIN</label><input id="pin-cur" type="password" inputmode="numeric" autocomplete="current-password"></div>
  <div class="field"><label class="label" for="pin-new">New PIN (6+ digits)</label><input id="pin-new" type="password" inputmode="numeric" autocomplete="new-password"></div></div>
  <div class="row-btns"><button class="btn" data-act="changePin">Change PIN</button><button class="btn" data-act="logout">Log out of scoring</button></div></div>

  </section>`;
}
function schedulePanel(){
  const list=Object.values(M).sort(byNo);if(!list.length)return"";
  const sc=ui.sched||(ui.sched={d1:"2026-11-29",d2:"2026-12-06",d3:"2026-12-13",start:"08:00",mins:75});
  const toLocal=w=>{if(!w)return"";const d=new Date(w);if(isNaN(d))return"";const p=n=>String(n).padStart(2,"0");return`${d.getFullYear()}-${p(d.getMonth()+1)}-${p(d.getDate())}T${p(d.getHours())}:${p(d.getMinutes())}`};
  return`<details class="card"><summary><span>Match schedule</span><span class="muted small">${list.filter(m=>m.when).length} of ${list.length} dated</span></summary><div class="in">
  <p class="kv">Fill the three match days and a start time, then <b>Auto-fill</b>: league matches 1–10 on day 1, 11–20 on day 2, knockouts on day 3, spaced by the minutes per match. Adjust any match below and <b>Save schedule</b>.</p>
  <div class="grid2"><div class="field"><label class="label" for="sc-d1">Day 1</label><input id="sc-d1" type="date" value="${sc.d1}" data-sc="d1"></div><div class="field"><label class="label" for="sc-d2">Day 2</label><input id="sc-d2" type="date" value="${sc.d2}" data-sc="d2"></div><div class="field"><label class="label" for="sc-d3">Day 3 (knockouts)</label><input id="sc-d3" type="date" value="${sc.d3}" data-sc="d3"></div>
  <div class="field"><label class="label" for="sc-start">First match starts</label><input id="sc-start" type="time" value="${sc.start}" data-sc="start"></div><div class="field"><label class="label" for="sc-mins">Minutes per match</label><input id="sc-mins" type="number" min="30" max="240" value="${sc.mins}" data-sc="mins"></div></div>
  <button class="btn sm" data-act="schedAuto">Auto-fill</button>
  <div class="schedlist">${list.map(m=>`<div class="prow"><span class="pn small"><b>${isLeague(m)?"M"+m.no:esc(m.stage)}</b> ${esc(tmeta(m.a).short)} v ${esc(tmeta(m.b).short)}</span><input type="datetime-local" value="${toLocal(ui.schedDraft?.[m.id]??m.when)}" data-when="${m.id}" aria-label="Date and time"></div>`).join("")}</div>
  <button class="btn pri" data-act="schedSave">Save schedule</button><div id="sc-msg"></div></div></details>`;
}
function roundRobin(ids){
  const a=[...ids];if(a.length%2)a.push(null);const n=a.length,rounds=[];
  for(let r=0;r<n-1;r++){const games=[];for(let i=0;i<n/2;i++){const x=a[i],y=a[n-1-i];if(x&&y)games.push(r%2?[y,x]:[x,y])}rounds.push(games);a.splice(1,0,a.pop())}
  return rounds;
}

/* ================= render ================= */
function render(){
  $("#hdr").innerHTML=headerHtml();
  const app=$("#app");
  if(fatal==="config"){app.innerHTML=`<section><div class="empty"><strong>Almost there</strong>Paste your Firebase settings into config.js, then upload the folder again.</div></section>`;return}
  if(fatal==="read"&&!loaded.m){app.innerHTML=`<section><div class="empty"><strong>Can't reach the scoreboard</strong>Check your connection and reload the page.</div></section>`;return}
  if(!loaded.t||!loaded.m){app.innerHTML=`<section><div class="empty"><strong>Loading scores…</strong>Connecting to the scoreboard.</div></section>`;return}
  if(!canScore&&(ui.tab==="score"||ui.tab==="setup"))ui.tab="live";
  if(KIDS&&(ui.tab==="fantasy"||ui.tab==="rules"||(ui.tab==="stats"&&ui.stat==="emerging"))){ui.tab=ui.tab==="stats"?"stats":"live";ui.stat="mvp"}
  const v={rules:rulesView,player:playerView,matches:matchesView,table:tableView,stats:statsView,fantasy:fantasyView,team:teamView,score:scoreView,setup:setupView,login:loginView}[ui.tab]||liveView;
  app.innerHTML=v();
}

/* ================= actions ================= */
function curMatch(){return M[ui.scoreSel]?clone(M[ui.scoreSel]):null}
function addBall(p){
  const m=curMatch();if(!m)return;const inn=last(m.inn);if(!inn||inn.closed)return;
  const b={...p,s:inn.cur.s,ns:inn.cur.ns,bw:inn.cur.bw};
  if(isFreeHit(inn))b.fh=true;
  inn.balls.push(b);
  let{s,ns,bw}=inn.cur;
  if(ns&&b.r%2===1)[s,ns]=[ns,s];
  if(invalidW(b))delete b.w;
  if(b.w){if(s===b.w.out)s=null;else if(ns===b.w.out)ns=null}
  const legal=inn.balls.filter(isLegal).length;
  if(isLegal(b)&&legal%6===0){[s,ns]=[ns,s];bw=null}
  inn.cur={s,ns,bw};
  checkEnd(m);
  ui.sheet=null;saveMatch(m);
}
function undo(){
  const m=curMatch();if(!m)return;const inn=last(m.inn);
  if(m.how==="super"){m.status="super";m.result="Scores level · Super Over to decide";m.winner=null;delete m.how;delete m.super;return saveMatch(m)}
  if(m.how==="nr"||m.how==="wo"){m.result="";m.winner=null;delete m.how;
    m.status=!inn?(m.toss?"setup":"scheduled"):(inn.closed&&m.inn.length===1?"break":"live");if(inn&&m.inn.length===2)inn.closed=false;return saveMatch(m)}
  if(!inn)return;
  m.result="";m.winner=null;delete m.how;delete m.super;
  if(inn.closed&&inn.manual){inn.closed=false;delete inn.manual;m.status="live";return saveMatch(m)}
  if(!inn.closed&&inn.balls.length===0){m.inn.pop();m.status=m.inn.length?"break":"setup";const p=last(m.inn);if(p&&p.manual){p.closed=false;delete p.manual;m.status="live"}return saveMatch(m)}
  if(!inn.balls.length)return;
  const b=inn.balls.pop();inn.cur={s:b.s,ns:b.ns,bw:b.bw};inn.closed=false;m.status="live";ui.sheet=null;saveMatch(m);
}
function endWith(m,winner,result,how){m.winner=winner;m.result=result;m.how=how;m.status="done";saveMatch(m)}
const acts={
  tab:el=>{ui.tab=el.dataset.v;ui.sheet=null;pendingConfirm=null;ui.loginErr="";if(ui.tab==="setup")ui.draft=null;if(ui.tab==="live")ui.sel=null;
    try{history.replaceState(null,"",["live","matches","table","stats","fantasy","rules"].includes(ui.tab)?"#"+ui.tab:location.pathname+location.search)}catch(e){}render();scrollTo(0,0)},
  view:el=>{ui.sel=el.dataset.id;ui.tab="live";render();scrollTo(0,0)},
  team:el=>{ui.teamId=el.dataset.id;ui.tab="team";render();scrollTo(0,0)},
  player:el=>{if(!pteam(el.dataset.id))return;ui.prev={tab:ui.tab,sel:ui.sel,teamId:ui.teamId,y:scrollY};ui.playerId=el.dataset.id;ui.tab="player";render();scrollTo(0,0)},
  pback:()=>{const p=ui.prev||{tab:"stats"};ui.tab=p.tab==="player"?"stats":p.tab;ui.sel=p.sel;ui.teamId=p.teamId;render();scrollTo(0,p.y||0)},
  card:el=>resultCard(M[el.dataset.id],el),
  unsel:()=>{ui.sel=null;render()},
  stat:el=>{ui.stat=el.dataset.v;render()},
  statTab:el=>{ui.stat=el.dataset.v;ui.tab="stats";render();scrollTo(0,0)},
  fopen:el=>{ui.fopen=ui.fopen===el.dataset.id?null:el.dataset.id;render();const p=$(".pickpanel");if(p)p.scrollIntoView({block:"nearest"})},
  fanSave:()=>{const v=($("#fan-name")?.value||"").trim();if(v.length<2){flash("Enter at least 2 characters.");return}FAN.name=v;try{localStorage.setItem("mc-fan",v)}catch(e){}if(uid&&db)setDoc(doc(db,C("fans"),uid),{name:v,uid},{merge:true}).catch(()=>{});render()},
  fNew:()=>{FT.draft={name:FAN.name||"",p:[]};FT.q="";FT.err="";render()},
  fEdit:()=>{FT.draft={name:FT.mine.name,p:[...FT.mine.p],c:FT.mine.c||null,vc:FT.mine.vc||null};FT.q="";FT.err="";render()},
  fSub:()=>{if(!SUBS.open||!FT.mine)return;const k=SUBS.phase,cur=verAt(FT.mine,k),base=verAt(FT.mine,k-1);FT.draft={mode:"sub",k,base:[...base.p],p:[...cur.p],c:cur.c||null,vc:cur.vc||null};FT.q="";FT.err="";render();scrollTo(0,0)},
  fCancel:()=>{FT.draft=null;render()},
  fTog:el=>{const d=FT.draft,id=el.dataset.id;const i=d.p.indexOf(id);if(i>=0){d.p.splice(i,1);if(d.c===id)d.c=null;if(d.vc===id)d.vc=null}else{const w=cantAdd(d.p,id,d.mode==="sub"?d.base:null);if(w){flash(w);return}d.p.push(id)}FT.err="";render()},
  fSave:()=>saveFantasy(),
  fForget:()=>{FT.myId=null;FT.mine=null;try{localStorage.removeItem(SK("mc-fid"))}catch(e){}render()},
  vote:el=>vote(el.dataset.m,el.dataset.t),
  cupVote:el=>cupVote(el.dataset.t),
  ssel:el=>{ui.scoreSel=el.dataset.id;ui.sheet=null;ui.toss=null;pendingConfirm=null;try{sessionStorage.setItem(SK("mc-score"),ui.scoreSel)}catch(e){}render()},
  newMatch:()=>{ui.scoreSel="new";const[a,b]=suggest("QF1");ui.nm={stage:"QF1",a:a||T.teams[0].id,b:b||T.teams[1].id};render()},
  createMatch:()=>{const nm=ui.nm;if(!nm||nm.a===nm.b)return;
    const no=Math.max(0,...Object.values(M).map(m=>m.no||0))+1;
    const m={id:uidGen("m"),no,stage:nm.stage,a:nm.a,b:nm.b,status:"scheduled",inn:[],result:"",winner:null,overs:T.overs};
    ui.scoreSel=m.id;ui.toss=null;saveMatch(m)},
  tossDone:()=>{const m=curMatch(),tz=ui.toss;m.toss=tz.toss;m.chose=tz.chose;m.xi=clone(tz.xi);m.overs=+tz.overs;m.status="setup";saveMatch(m)},
  redoToss:()=>{const m=curMatch();m.status="scheduled";ui.toss=null;saveMatch(m)},
  startInn:el=>{const m=curMatch();const s=$("#op-s").value,ns=$("#op-ns").value,bw=$("#op-bw").value;
    if(!s||!ns||!bw||s===ns){flash("Pick two different openers and a bowler.");return}
    m.inn.push({bat:el.dataset.bat,bowl:el.dataset.bowl,open:[s,ns],cur:{s,ns,bw},balls:[],closed:false});m.status="live";saveMatch(m)},
  pickBat:el=>{const m=curMatch();const v=$("#nb-sel")?.value;if(!v)return;last(m.inn).cur[el.dataset.slot]=v;saveMatch(m)},
  pickBowl:()=>{const m=curMatch();const v=$("#bw-sel")?.value;if(!v)return;last(m.inn).cur.bw=v;saveMatch(m)},
  changeBowler:()=>{const m=curMatch(),inn=last(m.inn);if(innStats(inn).cur.length){flash("The bowler can change only at the start of an over. Undo the balls first if this was a mistake.");return}inn.cur.bw=null;saveMatch(m)},
  run:el=>addBall({t:"run",r:+el.dataset.r}),
  sheet:el=>{ui.sheet={k:el.dataset.k,kind:null,wt:"run",out:"s",runs:0,f:""};render()},
  closeSheet:()=>{ui.sheet=null;render()},
  fixInn:el=>{ui.sheet.ii=+el.dataset.v;ui.sheet.idx=null;render()},
  fixBack:()=>{ui.sheet.idx=null;render()},
  fixPick:el=>{const m=M[ui.scoreSel],ii=ui.sheet.ii??m.inn.length-1,b=m.inn[ii].balls[+el.dataset.v];
    ui.sheet.ii=ii;ui.sheet.idx=+el.dataset.v;ui.sheet.d={s:b.s,ns:b.ns,bw:b.bw,t:b.t,r:b.r,wk:b.w?.k||"",out:b.w?.out||b.s,f:b.w?.f||"",batLater:true,bwOver:true};render()},
  fixSave:()=>{const m=curMatch(),s=ui.sheet,ii=s.ii,inn=m.inn[ii],idx=s.idx,d=s.d,old=inn.balls[idx];
    {const prev=inn.balls[idx-1];const fh=T.freeHit&&prev&&(prev.t==="nb"||(prev.fh&&prev.t==="wd"));const ok=d.t==="nb"||fh?["ro"]:d.t==="wd"?["ro","st"]:null;
      if(d.wk&&ok&&!ok.includes(d.wk)){flash(`A batter can only be ${ok.map(x=>KINDS.find(k=>k[0]===x)[1].toLowerCase()).join(" or ")} off that delivery.`);return}}
    const repl=(obj,from,to)=>{if(!from||from===to)return;["s","ns"].forEach(k=>{if(obj[k]===from)obj[k]=to});if(obj.w&&obj.w.out===from)obj.w.out=to};
    // batter substitutions
    [["s",old.s,d.s],["ns",old.ns,d.ns]].forEach(([k,from,to])=>{if(from===to)return;
      if(d.batLater){for(let i=idx;i<inn.balls.length;i++)repl(inn.balls[i],from,to);repl(inn.cur,from,to);inn.open=(inn.open||[]).map(x=>x===from?to:x)}else{inn.balls[idx][k]=to}});
    // bowler
    if(old.bw!==d.bw){if(d.bwOver){const lab=innStats(inn).log[idx].lab.split(".")[0];innStats(inn).log.forEach((e,i)=>{if(e.lab.split(".")[0]===lab&&inn.balls[i].bw===old.bw)inn.balls[i].bw=d.bw});if(inn.cur.bw===old.bw)inn.cur.bw=d.bw}else inn.balls[idx].bw=d.bw}
    const b=inn.balls[idx];b.t=d.t;b.r=+d.r;
    if(d.wk){b.w={k:d.wk,out:d.out};if(d.f)b.w.f=d.f}else delete b.w;
    inn.balls.forEach((x,i)=>{const p=inn.balls[i-1];const fh=T.freeHit&&p&&(p.t==="nb"||(p.fh&&p.t==="wd"));if(fh)x.fh=true;else delete x.fh});
    // re-evaluate end state
    if(ii===m.inn.length-1&&(m.status==="live"||m.status==="break"||m.status==="done")){const was=m.status;inn.closed=false;if(inn.manual){/* keep manual close */inn.closed=true}else{m.status="live";m.result="";m.winner=null;delete m.how;checkEnd(m);if(m.status==="live"&&was!=="live"&&!inn.manual){/* reopened: fine */}}}
    ui.sheet=null;saveMatch(m);flash("Ball fixed and totals recalculated.",true)},
  ext:el=>addBall({t:ui.sheet.k,r:+el.dataset.r}),
  wk:el=>{ui.sheet.kind=el.dataset.v;if(el.dataset.v!=="ro"&&el.dataset.v!=="st")ui.sheet.wt="run";render()},
  wo:el=>{ui.sheet.out=el.dataset.v;render()},
  wr:el=>{ui.sheet.runs=+el.dataset.v;render()},
  wt:el=>{ui.sheet.wt=el.dataset.v;render()},
  wkConfirm:()=>{const s=ui.sheet,m=M[ui.scoreSel],c=last(m.inn).cur;
    const w={k:s.kind,out:s.kind==="ro"&&s.out==="ns"?c.ns:c.s};const f=$("#wk-f")?.value;if(f)w.f=f;
    addBall({t:s.wt,r:s.kind==="ro"?s.runs:0,w})},
  undo:()=>undo(),
  swap:()=>{const m=curMatch(),c=last(m.inn).cur;if(!c.ns)return;[c.s,c.ns]=[c.ns,c.s];saveMatch(m)},
  endInn:()=>ask("End this innings now? Use this only if play was cut short. Undo reopens it.","End innings",()=>{const m=curMatch();last(m.inn).manual=true;closeInn(m);saveMatch(m)}),
  saveSettings:()=>{const m=curMatch();m.overs=+$("#ms-overs").value;const o2=$("#ms-ov2"),tg=$("#ms-tgt");
    if(o2)m.ov2=o2.value?+o2.value:null;if(tg)m.tgt=tg.value?Math.max(1,parseInt(tg.value,10)):null;
    if(m.status==="live"&&m.inn.length)checkEnd(m);saveMatch(m);flash("Match settings applied.",true)},
  noResult:()=>ask("Record this match as no result? Both teams get 1 point and it does not count toward net run rate.","No result",()=>endWith(curMatch(),"nr","No result · 1 point each","nr")),
  walkover:el=>{const w=el.dataset.w;ask(`Award a walkover to ${tname(w)}?`,"Award walkover",()=>endWith(curMatch(),w,`${tname(w)} won by walkover`,"wo"))},
  superWin:el=>{const m=curMatch(),w=el.dataset.w;m.super=($("#so-score")?.value||"").trim();endWith(m,w,`${tname(w)} won the Super Over`,"super")},
  delMatch:()=>ask(`Delete ${stageLabel(M[ui.scoreSel]||{})}? Its scores are removed for everyone.`,"Delete match",()=>{const id=ui.scoreSel;delete M[id];ui.scoreSel=null;if(ui.sel===id)ui.sel=null;render();delMatchDoc(id);
    if(!fantasyLocked()){fantasyLockWritten=false;deleteDoc(doc(db,C("meta"),"lock")).catch(()=>{})}}),
  confirmYes:()=>{const f=pendingConfirm?.fn;pendingConfirm=null;if(f)f();else render()},
  confirmNo:()=>{pendingConfirm=null;render()},
  importTeams:()=>{
    const txt=$("#imp-text").value;const blocks=[];let cur=null;
    const tidy=v=>v.replace(/^\s*[:\-–]\s*/,"").replace(/\s+/g," ").trim();
    const cap=v=>v.toLowerCase().replace(/(^|\s)\S/g,c=>c.toUpperCase());
    for(const raw of txt.split(/\r?\n/)){const line=raw.trim();if(!line)continue;
      let m=line.match(/^team(?:\s*name)?\.?\s*[:\-–]\s*(.+)$/i);
      if(m){cur={name:m[1].trim().toUpperCase(),players:[]};blocks.push(cur);continue}
      if(!cur)continue;
      m=line.match(/^icon(?:\s*name)?\.?\s*[:\-–]\s*(.+)$/i);
      if(m){cur.players.unshift(cap(m[1].trim()));continue}
      m=line.match(/^(?:marquee|player\s*\d*)\s*[:\-–]\s*(.+)$/i);
      cur.players.push(cap(tidy(m?m[1]:line)));}
    if(!blocks.length){flashAt("imp-msg","No teams found. Each team needs a line starting with Team.");return}
    const d=ui.draft;let added=0,merged=0;
    blocks.forEach((b,i)=>{let t=d.teams.find(x=>x.name.trim().toUpperCase()===b.name);
      if(!t){t=d.teams.find(x=>!x.name.trim()&&!x.players.some(p=>p.name.trim()));
        if(t){t.name=b.name}else{t={id:uidGen("t"),name:b.name,group:"A",players:[]};d.teams.push(t)}
        t.group=d.teams.filter(x=>x.name.trim()).indexOf(t)<5?"A":"B";added++}else merged++;
      const have=new Set(t.players.map(p=>p.name.trim().toLowerCase()));
      b.players.forEach(n=>{if(have.has(n.toLowerCase()))return;const np=poolPlayer(n);const slot=t.players.find(p=>!p.name.trim());if(slot)Object.assign(slot,{name:np.name,reg:np.reg,role:np.role});else t.players.push(np);have.add(n.toLowerCase())});
    });
    render();flashAt("imp-msg",`${added} team${added===1?"":"s"} added, ${merged} updated. Check the groups, then Save teams.`,true)},
  schedAuto:()=>{const sc=ui.sched;const list=Object.values(M).sort(byNo);const lg=list.filter(isLeague),ko=list.filter(m=>!isLeague(m));
    const mk=(date,i)=>{const [h,mi]=sc.start.split(":").map(Number);const d=new Date(`${date}T00:00`);d.setMinutes(h*60+mi+i*(+sc.mins||75));return d.toISOString()};
    ui.schedDraft={};lg.forEach((m,i)=>{ui.schedDraft[m.id]=i<10?mk(sc.d1,i):mk(sc.d2,i-10)});ko.forEach((m,i)=>ui.schedDraft[m.id]=mk(sc.d3,i));render()},
  schedSave:async()=>{const d=ui.schedDraft||{};const b=writeBatch(db);let n=0;Object.values(M).forEach(m=>{const v=d[m.id];if(v!==undefined&&v!==(m.when||"")){const w=v?new Date(v).toISOString():null;const mm={...m};if(w)mm.when=w;else delete mm.when;M[m.id]=mm;b.set(doc(db,C("matches"),m.id),strip(mm));n++}});
    try{await b.commit();ui.schedDraft=null;render();flashAt("sc-msg",`${n} match${n===1?"":"es"} updated.`,true)}catch(e){flashAt("sc-msg","Not saved. Check your connection.")}},
  addTeam:()=>{ui.draft.teams.push({id:uidGen("t"),name:"",group:"B",players:Array.from({length:DEF.squad},()=>({id:uidGen("p"),name:""}))});render()},
  delTeam:el=>{ui.draft.teams=ui.draft.teams.filter(t=>t.id!==el.dataset.id);render()},
  addPlayer:el=>{ui.draft.teams.find(t=>t.id===el.dataset.id).players.push({id:uidGen("p"),name:""});render()},
  delPlayer:el=>{const[tid,pid]=el.dataset.id.split(":");const t=ui.draft.teams.find(t=>t.id===tid);t.players=t.players.filter(p=>p.id!==pid);render()},
  saveSetup:()=>{const d=clone(ui.draft);d.name=(d.name||"").trim()||DEF.name;
    d.wideRuns=Math.max(0,parseInt(d.wideRuns,10)||0);d.nbRuns=Math.max(0,parseInt(d.nbRuns,10)||0);
    d.teams=d.teams.map(t=>({id:t.id,name:(t.name||"").trim(),group:t.group,players:t.players.map(p=>{const o={id:p.id,name:(p.name||"").trim()};if(p.reg)o.reg=p.reg;if(p.role)o.role=p.role;if(p.age)o.age=p.age;return o}).filter(p=>p.name)})).filter(t=>t.name||t.players.length);
    const short=d.teams.find(t=>t.players.length<DEF.minXi);
    const started=Object.values(M).some(m=>(m.inn||[]).length);
    const bad=d.teams.length<2?"Add at least two teams with names.":d.teams.find(t=>!t.name)?"Every team needs a name.":(short&&started)?`${short.name} needs at least ${DEF.minXi} players.`:"";
    if(bad){flash(bad);return}
    T=d;ui.draft=clone(d);
    setDoc(doc(db,C("tournament"),"main"),strip(d)).then(()=>flash(short?`Saved. ${short.name} has under ${DEF.minXi} players; finish the squads before match day.`:"Saved. Everyone sees these teams now.",true)).catch(e=>flash(e?.code==="permission-denied"?"Not saved: log in as scorer again.":"Not saved. Check your connection."));
    render();flash("Saving…",true)},
  fixtures:()=>{const rr={A:roundRobin(T.teams.filter(t=>t.group==="A").map(t=>t.id)),B:roundRobin(T.teams.filter(t=>t.group==="B").map(t=>t.id))};
    let no=Math.max(0,...Object.values(M).map(m=>m.no||0));const rounds=Math.max(rr.A.length,rr.B.length);const batch=writeBatch(db);
    for(let r=0;r<rounds;r++)for(const g of["A","B"])for(const[a,b]of rr[g][r]||[]){const m={id:uidGen("m"),no:++no,stage:g,a,b,status:"scheduled",inn:[],result:"",winner:null,overs:T.overs,upd:Date.now()};M[m.id]=m;batch.set(doc(db,C("matches"),m.id),m)}
    batch.commit().catch(()=>flash("Fixtures not saved. Check your connection."));render();flash(`${no} league matches created. Find them under Score and Matches.`,true)},
  pubBoard:()=>publishBoard(true),
  subsOpen:()=>ask(`Open the substitution window for match day ${SUBS.phase+2}? Fans can then make up to 2 changes until the next first ball.`,"Open window",async()=>{await setSubs({phase:SUBS.phase+1,open:true});await publishBoard();render();flash("Substitution window open.",true)}),
  subsClose:()=>ask("Close the substitution window now?","Close window",async()=>{await setSubs({phase:SUBS.phase,open:false});await publishBoard();render();flash("Substitution window closed.",true)}),
  dlBackup:()=>{try{const ist=new Date(Date.now()+19800000).toISOString().slice(0,16).replace("T","-").replace(":","");
    const blob=new Blob([JSON.stringify({at:new Date().toISOString(),cup:KIDS?"kids":"adults",tournament:T,matches:M},null,1)],{type:"application/json"});
    const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download=`mascon-${KIDS?"kids-":""}backup-${ist}.json`;document.body.appendChild(a);a.click();
    setTimeout(()=>{URL.revokeObjectURL(a.href);a.remove()},2000);flash("Backup file saved to this phone's downloads.",true)}catch(e){flash("Could not save the file on this phone.")}},
  demoSim:()=>demoPlayDay(),
  demoExit:()=>{location.href=location.pathname+(KIDS?"?cup=kids":"")},
  changePin:async()=>{const cur=$("#pin-cur").value,nw=$("#pin-new").value;
    if(nw.length<6){flash("The new PIN needs at least 6 digits.");return}
    try{await reauthenticateWithCredential(auth.currentUser,EmailAuthProvider.credential(CFG.scorerEmail,cur));await updatePassword(auth.currentUser,nw);flash("PIN changed. Share the new PIN with your scorers.",true)}
    catch(e){flash(e?.code==="auth/wrong-password"||e?.code==="auth/invalid-credential"?"Current PIN is wrong.":"PIN not changed. Try again.")}},
  logout:()=>{signOut(auth);ui.tab="live";render()},
  reset:()=>ask("Delete the tournament, all teams, every match, all predictions and all fantasy teams? This cannot be undone.","Delete everything",async()=>{
    try{const batch=writeBatch(db);Object.keys(M).forEach(id=>{batch.delete(doc(db,C("matches"),id));batch.delete(doc(db,C("polls"),id))});batch.delete(doc(db,C("tournament"),"main"));batch.delete(doc(db,C("meta"),"lock"));
      const fs=await getDocs(collection(db,C("fantasy")));const fn=await getDocs(collection(db,C("fans")));let b2=batch,n=0;const extra=[];
      [...fs.docs,...fn.docs].forEach(d=>{if(n++>=400){b2=writeBatch(db);extra.push(b2);n=1}b2.delete(d.ref)});
      await batch.commit();for(const b of extra)await b.commit();
      fantasyLockWritten=false;M={};T=null;ui.draft=null;ui.scoreSel=null;ui.sel=null;FT.all=null;FT.mine=null;render();flash("Everything deleted.",true)}
    catch(e){flash("Not fully deleted. Check your connection and try again.")}}),
  realSetup:()=>ask(T?"Replace the current teams and matches with the real tournament setup (10 franchises, icons, 20 fixtures)? Scores and fantasy entries are deleted.":"Set up the real tournament now? 10 franchises with icons and 20 league fixtures.","Set up",async()=>{
    flashAt("qs-msg","Setting up…",true);
    try{const wipe=writeBatch(db);Object.keys(M).forEach(id=>{wipe.delete(doc(db,C("matches"),id));wipe.delete(doc(db,C("polls"),id))});wipe.delete(doc(db,C("meta"),"lock"));
      const fs=await getDocs(collection(db,C("fantasy")));fs.docs.forEach(x=>wipe.delete(x.ref));await wipe.commit();
      const d={...clone(DEF),teams:blankTeams()};d.teams=d.teams.map(t=>({id:t.id,name:t.name,group:t.group,players:t.players.filter(p=>p.name)}));
      const b=writeBatch(db);b.set(doc(db,C("tournament"),"main"),strip(d));
      const rr={A:roundRobin(d.teams.filter(t=>t.group==="A").map(t=>t.id)),B:roundRobin(d.teams.filter(t=>t.group==="B").map(t=>t.id))};let no=0;
      for(let r=0;r<Math.max(rr.A.length,rr.B.length);r++)for(const g of["A","B"])for(const[a,bb]of rr[g][r]||[]){const mid=uidGen("m");b.set(doc(db,C("matches"),mid),{id:mid,no:++no,stage:g,a,b:bb,status:"scheduled",inn:[],result:"",winner:null,overs:d.overs,upd:Date.now()})}
      await b.commit();fantasyLockWritten=false;FT.all=null;ui.draft=null;ui.scoreSel=null;ui.sel=null;render();flashAt("qs-msg",`Done: 10 teams and ${no} league fixtures created. Assign players from the Auction pool after 1 November.`,true)}
    catch(e){flashAt("qs-msg","Setup failed. Check your connection and try again.")}}),
  loadDemo:()=>ask("Load the demo tournament? This replaces everything currently saved (teams, matches, predictions, fantasy teams) with simulated data.","Load demo",async()=>{
    flashAt("qs-msg","Loading demo…",true);
    try{const r=await fetch("demo.json",{cache:"no-store"});if(!r.ok)throw new Error("fetch");const d=await r.json();
      // wipe first
      const wipe=writeBatch(db);Object.keys(M).forEach(id=>{wipe.delete(doc(db,C("matches"),id));wipe.delete(doc(db,C("polls"),id))});wipe.delete(doc(db,C("meta"),"lock"));
      const fs=await getDocs(collection(db,C("fantasy")));fs.docs.forEach(x=>wipe.delete(x.ref));await wipe.commit();
      const b=writeBatch(db);b.set(doc(db,C("tournament"),"main"),d.tournament);
      Object.values(d.matches).forEach(m=>b.set(doc(db,C("matches"),m.id),{...m,upd:Date.now()}));
      (d.fantasy||[]).forEach(f=>b.set(doc(db,C("fantasy"),f.id),{name:f.name,p:f.p,uid:f.uid,at:Date.now(),demo:true}));
      b.set(doc(db,C("meta"),"lock"),{at:Date.now(),demo:true});
      await b.commit();fantasyLockWritten=true;FT.all=null;ui.draft=null;ui.scoreSel=null;ui.sel=null;ui.tab="live";render();flash("Demo loaded.",true)}
    catch(e){flashAt("qs-msg",e?.code==="permission-denied"?"Demo not loaded: paste the latest firestore.rules into Firebase first.":"Demo not loaded. Check your connection.")}}),
};
function flashAt(id,msg,good){const el=$("#"+id);if(el)el.innerHTML=`<div class="msg" style="color:var(${good?"--good":"--out"})">${esc(msg)}</div>`}
function flash(msg,good){
  let el=ui.tab==="setup"?$("#setup-msg"):null;
  if(!el){el=document.createElement("div");$("#app section")?.prepend(el)}
  el.innerHTML=`<div class="msg" style="color:var(${good?"--good":"--out"})">${esc(msg)}</div>`;
}
document.addEventListener("click",e=>{const el=e.target.closest("[data-act]");if(!el||el.disabled)return;const f=acts[el.dataset.act];if(f){e.preventDefault();f(el)}});
document.addEventListener("submit",async e=>{
  if(e.target.id!=="login-form")return;e.preventDefault();
  const pin=$("#pin").value.trim();if(!pin)return;
  ui.busyLogin=true;ui.loginErr="";render();
  try{await signInWithEmailAndPassword(auth,CFG.scorerEmail,pin);ui.tab="score"}
  catch(err){ui.loginErr=err?.code==="auth/too-many-requests"?"Too many tries. Wait a few minutes and try again.":err?.code==="auth/network-request-failed"?"No connection. Try again when you have signal.":"Wrong PIN."}
  ui.busyLogin=false;render();
});
document.addEventListener("input",e=>{
  const t=e.target;
  if(t.dataset.fname&&FT.draft){FT.draft.name=t.value;return}
  if(t.dataset.fanname)return;
  if(t.dataset.sc&&ui.sched){ui.sched[t.dataset.sc]=t.value;return}
  if(t.dataset.when){(ui.schedDraft||(ui.schedDraft={}))[t.dataset.when]=t.value;return}
  if(t.dataset.poolq){ui.poolQ=t.value;const sc=scrollY;render();const q=$("#pool-q");if(q){q.focus();q.setSelectionRange(q.value.length,q.value.length)}scrollTo(0,sc);return}
  if(t.dataset.fq){FT.q=t.value;renderDeferred=false;const sc=scrollY;render();const q=$("#f-q");if(q){q.focus();q.setSelectionRange(q.value.length,q.value.length)}scrollTo(0,sc);return}
  const d=ui.draft;if(!d)return;
  if(t.dataset.bind)d[t.dataset.bind]=t.value;
  else if(t.dataset.tname)d.teams.find(x=>x.id===t.dataset.tname).name=t.value;
  else if(t.dataset.pname){const[tid,pid]=t.dataset.pname.split(":");d.teams.find(x=>x.id===tid).players.find(p=>p.id===pid).name=t.value}
});
document.addEventListener("change",e=>{
  const t=e.target;
  if(t.dataset.pool&&ui.draft){const reg=+t.dataset.pool,d=ui.draft,P=POOL.find(x=>x.reg===reg);
    d.teams.forEach(x=>{x.players=x.players.filter(p=>!(p.reg===reg||(!p.reg&&p.name.trim().toLowerCase()===P.name.toLowerCase())))});
    if(t.value){const tm=d.teams.find(x=>x.id===t.value);const slot=tm.players.find(p=>!p.name.trim());const np={id:slot?slot.id:uidGen("p"),name:P.name,reg:P.reg,role:P.role,age:P.age};if(slot)Object.assign(slot,np);else tm.players.push(np)}
    const sc=scrollY;render();scrollTo(0,sc);return}
  if(t.dataset.poolall){ui.poolAll=t.checked;render();return}
  if(t.dataset.donesel){if(t.value){ui.scoreSel=t.value;ui.sheet=null;ui.toss=null;pendingConfirm=null;try{sessionStorage.setItem(SK("mc-score"),t.value)}catch(e){}render()}return}
  if(t.dataset.tgroup&&ui.draft){ui.draft.teams.find(x=>x.id===t.dataset.tgroup).group=t.value;t.blur();render()}
  if(t.dataset.nm&&ui.nm){ui.nm[t.dataset.nm]=t.value;if(t.dataset.nm==="stage"){const[a,b]=suggest(t.value);if(a)ui.nm.a=a;if(b)ui.nm.b=b}t.blur();render()}
  if(t.dataset.tz&&ui.toss){ui.toss[t.dataset.tz]=t.value;t.blur();render()}
  if(t.dataset.xi&&ui.toss){const[team,pid]=t.dataset.xi.split(":");const arr=ui.toss.xi[team];
    if(t.checked){if(!arr.includes(pid))arr.push(pid)}else ui.toss.xi[team]=arr.filter(x=>x!==pid);t.blur();render()}
  if(t.id==="wk-f"&&ui.sheet)ui.sheet.f=t.value;
  if(t.dataset.fix&&ui.sheet?.d){const k=t.dataset.fix,d=ui.sheet.d;d[k]=t.type==="checkbox"?t.checked:(k==="r"?+t.value:t.value);
    if(k==="t"){const ok=d.t==="nb"?["ro"]:d.t==="wd"?["ro","st"]:null;if(d.wk&&ok&&!ok.includes(d.wk))d.wk="";t.blur();render()}
    if(k==="wk"){t.blur();render()}}
  if(t.dataset.fpick&&FT.draft){const d=FT.draft,id=t.dataset.fpick;const i=d.p.indexOf(id);
    if(t.checked&&i<0){const w=cantAdd(d.p,id,d.mode==="sub"?d.base:null);if(w){t.checked=false;flash(w);return}d.p.push(id)}
    else if(!t.checked&&i>=0){d.p.splice(i,1);if(d.c===id)d.c=null;if(d.vc===id)d.vc=null}
    FT.err="";const sc=scrollY;render();scrollTo(0,sc)}
  if(t.dataset.fcap&&FT.draft){const d=FT.draft,k=t.dataset.fcap;d[k]=t.value||null;if(k==="c"&&d.vc===d.c)d.vc=null;if(k==="vc"&&d.c===d.vc)d.c=null;FT.err="";const sc=scrollY;render();scrollTo(0,sc)}
});

render();
try{welcomeShow()}catch(e){}
/* ===== "Add to home screen": slim bar at the very top of the page until the app is installed.
   ✕ hides it for this visit only; it comes back next time until the icon is added. ===== */
let installEvt=null;addEventListener("beforeinstallprompt",e=>{e.preventDefault();installEvt=e;showInstallTip()});
function a2hsSteps(){
  const ua=navigator.userAgent,ios=/iPhone|iPad|iPod/i.test(ua),inApp=/WhatsApp|FBAN|FBAV|Instagram/i.test(ua);
  return ios?(inApp?"Open this link in <b>Safari</b>, tap Share ⬆, then <b>Add to Home Screen</b>.":"Tap Share ⬆ at the bottom of Safari, then <b>Add to Home Screen</b>.")
    :(inApp?"Open this link in <b>Chrome</b>, tap ⋮ at the top right, then <b>Add to Home screen</b>.":"Tap ⋮ at the top right of Chrome, then <b>Add to Home screen</b>.");
}
function showInstallTip(){
  if(DEMO||matchMedia("(display-mode: standalone)").matches||navigator.standalone)return;
  try{if(sessionStorage.getItem("mc-a2hs-x")==="1")return}catch(e){}
  let el=document.getElementById("a2hs");
  if(!el){el=document.createElement("div");el.id="a2hs";el.className="a2hs";document.body.insertBefore(el,document.body.firstChild)}
  el.innerHTML=`<img src="brand/icon-192.png" alt=""><span class="a2hs-t"><b>Add Mascon Cup to your home screen</b><span class="a2hs-how" hidden>${a2hsSteps()}</span></span><button class="btn pri sm" id="a2hs-go">${installEvt?"Add":"How?"}</button><button class="a2hs-x" aria-label="Close">✕</button>`;
  el.querySelector(".a2hs-x").onclick=()=>{el.remove();try{sessionStorage.setItem("mc-a2hs-x","1")}catch(e){}};
  el.querySelector("#a2hs-go").onclick=async()=>{
    if(installEvt){try{installEvt.prompt();const r=await installEvt.userChoice;if(r&&r.outcome==="accepted")el.remove()}catch(e){}installEvt=null;showInstallTip();return}
    const h=el.querySelector(".a2hs-how");h.hidden=!h.hidden};
}
addEventListener("appinstalled",()=>document.getElementById("a2hs")?.remove());
showInstallTip();
for(const k of["reset","loadDemo","realSetup"])acts[k]=()=>flash("This tool is switched off to protect the tournament data.");
try{boot()}catch(e){fatal="read";loaded={t:true,m:true};render()}

/* exported for tests */
window.__mc={fantasyPoints,innStats,finalize,pointsTable,tourStats,matrix,specials,bowlerOptions,roundRobin,set:(t,m)=>{T=t;M=m}};
