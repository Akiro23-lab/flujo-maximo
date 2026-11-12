"use strict";
/* =========================================================
   MODELO: grafo dirigido acíclico y Ford-Fulkerson
   ========================================================= */
const LETRAS = "abcdefghijklmnop";
const INF = "∞";
const K = (u, v) => u * 64 + v;
const KU = k => Math.floor(k / 64), KV = k => k % 64;
const letra = i => LETRAS[i];

class Grafo {
  constructor(n) {
    if (!(n >= 2 && n <= 16)) throw new Error("El modelo admite entre 2 y 16 nodos.");
    this.n = n; this.n0 = n; this.cap = new Map();
    this.S = null; this.T = null; this.fuentes = [0]; this.sumideros = [n - 1];
    this.fc = []; this.sc = []; this.evitar = false;
    this.reiniciar();
  }
  reiniciar() {
    this.flujo = new Map(); for (const k of this.cap.keys()) this.flujo.set(k, 0);
    this.flujoMax = 0; this.hist = []; this.caminos = []; this.corte = null;
    this.fuente = null; this.sumidero = null;
  }
  nombre(x) { if (x === this.S) return "S"; if (x === this.T) return "T"; return letra(x); }
  esF(u, v) { return Math.max(u, v) >= this.n0; }
  aristas() { return [...this.cap.entries()].map(([k, c]) => [KU(k), KV(k), c]).sort((a, b) => a[0] - b[0] || a[1] - b[1]); }
  originales() { return this.aristas().filter(([u, v]) => !this.esF(u, v)); }
  vecinos(x) { return this.aristas().filter(a => a[0] === x).map(a => a[1]); }
  entrantes(x) { return this.aristas().filter(a => a[1] === x).map(a => a[0]); }
  get tf() { return this.S !== null ? this.S : this.fuentes[0]; }
  get ts() { return this.T !== null ? this.T : this.sumideros[0]; }
  ordenTopo() {
    const gr = Array(this.n).fill(0), ad = Array.from({ length: this.n }, () => []);
    for (const [u, v] of this.aristas()) { gr[v]++; ad[u].push(v); }
    const cola = []; for (let i = 0; i < this.n; i++) if (!gr[i]) cola.push(i);
    const orden = [];
    while (cola.length) { const u = cola.shift(); orden.push(u); for (const v of ad[u]) if (--gr[v] === 0) cola.push(v); }
    return orden;
  }
  buscarRuta(o, d) {
    const padre = new Map([[o, null]]), cola = [o];
    while (cola.length) { const x = cola.shift(); if (x === d) break; for (const y of this.vecinos(x)) if (!padre.has(y)) { padre.set(y, x); cola.push(y); } }
    if (!padre.has(d)) return null;
    const r = []; let x = d; while (x !== null) { r.push(x); x = padre.get(x); } return r.reverse();
  }
  agregar(u, v, c, reemplazar = false) {
    if (!(u >= 0 && u < this.n0 && v >= 0 && v < this.n0)) throw new Error(`Usa vértices de a a ${letra(this.n0 - 1)}.`);
    if (u === v) throw new Error("Una arista no puede conectar un nodo consigo mismo.");
    if (!Number.isInteger(c) || c <= 0) throw new Error("La capacidad debe ser un número entero mayor que cero.");
    const k = K(u, v);
    if (this.cap.has(k) && !reemplazar) throw new Error("La arista ya existe.");
    if (!this.cap.has(k)) {
      const r = this.buscarRuta(v, u);
      if (r) throw new Error(`La arista ${this.nombre(u)} → ${this.nombre(v)} crearía el ciclo ${[u, ...r].map(x => this.nombre(x)).join(" → ")}. El grafo debe ser dirigido y sin ciclos: cambia el sentido o elimina otra arista del ciclo.`);
    }
    this.cap.set(k, c); this.actFict(); this.reiniciar();
  }
  eliminar(u, v) {
    if (this.esF(u, v)) throw new Error("Las aristas ficticias no se editan.");
    this.cap.delete(K(u, v)); this.actFict(); this.reiniciar();
  }
  destinosValidos(u) { const r = []; for (let v = 0; v < this.n0; v++) if (v !== u && (this.cap.has(K(u, v)) || !this.buscarRuta(v, u))) r.push(v); return r; }
  entradasOrig(x) { return this.entrantes(x).filter(u => u < this.n0); }
  salidasOrig(x) { return this.vecinos(x).filter(v => v < this.n0); }
  fuentesPosibles() { const r = []; for (let u = 0; u < this.n0; u++) if (!this.entradasOrig(u).length && this.salidasOrig(u).length) r.push(u); return r; }
  sumiderosPosibles() { const r = []; for (let u = 0; u < this.n0; u++) if (this.entradasOrig(u).length && !this.salidasOrig(u).length) r.push(u); return r; }
  eliminarFict() {
    for (const k of [...this.cap.keys()]) if (Math.max(KU(k), KV(k)) >= this.n0) this.cap.delete(k);
    this.n = this.n0; this.S = this.T = null; this.fc = []; this.sc = []; this.reiniciar();
  }
  definirTerminales(f, s) {
    f = [...new Set(f)].sort((a, b) => a - b); s = [...new Set(s)].sort((a, b) => a - b);
    if (!f.length || !s.length) throw new Error("Elige al menos una fuente y un sumidero.");
    const comunes = f.filter(x => s.includes(x));
    if (comunes.length) throw new Error("Un vértice no puede ser fuente y sumidero a la vez: " + comunes.map(letra).join(", "));
    this.eliminarFict(); this.fuentes = f; this.sumideros = s;
    if (f.length > 1) { this.S = this.n++; this.fc = [...f]; }
    if (s.length > 1) { this.T = this.n++; this.sc = [...s]; }
    this.actFict(); this.reiniciar();
  }
  actFict() {
    const inf = this.originales().reduce((a, [, , c]) => a + c, 0) + 1;
    if (this.S !== null) for (const x of this.fc) this.cap.set(K(this.S, x), inf);
    if (this.T !== null) for (const x of this.sc) this.cap.set(K(x, this.T), inf);
  }
  textoCap(u, v, valor) { return this.esF(u, v) ? INF : String(valor === undefined ? this.cap.get(K(u, v)) : valor); }

  /* ---- apoyo: máximo flujo con capacidades dadas (Edmonds-Karp) ---- */
  static maxDirecto(caps, s, t) {
    const res = new Map(), vec = new Map();
    const add = (a, b) => { if (!vec.has(a)) vec.set(a, new Set()); vec.get(a).add(b); };
    for (const [k, c] of caps) { if (c <= 0) continue; const u = KU(k), v = KV(k); res.set(K(u, v), (res.get(K(u, v)) || 0) + c); if (!res.has(K(v, u))) res.set(K(v, u), 0); add(u, v); add(v, u); }
    let total = 0;
    for (;;) {
      const padre = new Map([[s, null]]), cola = [s];
      while (cola.length && !padre.has(t)) { const x = cola.shift(); for (const y of (vec.get(x) || [])) if (!padre.has(y) && res.get(K(x, y)) > 0) { padre.set(y, x); cola.push(y); } }
      if (!padre.has(t)) return total;
      let d = Infinity, y = t; while (padre.get(y) !== null) { const x = padre.get(y); d = Math.min(d, res.get(K(x, y))); y = x; }
      y = t; while (padre.get(y) !== null) { const x = padre.get(y); res.set(K(x, y), res.get(K(x, y)) - d); res.set(K(y, x), res.get(K(y, x)) + d); y = x; }
      total += d;
    }
  }
  libres(flujo, soloPositivas = true) {
    const m = new Map();
    for (const [k, c] of this.cap) { const l = c - flujo.get(k); if (!soloPositivas || l > 0) m.set(k, l); }
    return m;
  }
  *caminosDirectos(s, t, libres) {
    const sal = new Map();
    for (const k of [...libres.keys()].sort((a, b) => a - b)) if (libres.get(k) > 0) { const u = KU(k); if (!sal.has(u)) sal.set(u, []); sal.get(u).push(KV(k)); }
    const ruta = [s], en = new Set([s]);
    function* dfs(u) {
      if (u === t) { const r = []; for (let i = 0; i + 1 < ruta.length; i++) r.push([ruta[i], ruta[i + 1]]); yield r; return; }
      for (const v of (sal.get(u) || [])) { if (en.has(v)) continue; ruta.push(v); en.add(v); yield* dfs(v); ruta.pop(); en.delete(v); }
    }
    yield* dfs(s);
  }
  caminosResiduales(s, t, flujo) {
    const sal = new Map(); const push = (a, x) => { if (!sal.has(a)) sal.set(a, []); sal.get(a).push(x); };
    for (const [u, v, c] of this.aristas()) { const f = flujo.get(K(u, v)); if (c > f) push(u, [v, 1, c - f]); if (f > 0) push(v, [u, -1, f]); }
    const cand = [], ruta = [], en = new Set([s]);
    const dfs = u => {
      if (cand.length >= 250) return;
      if (u === t) { if (ruta.some(p => p[2] === -1)) cand.push(ruta.slice()); return; }
      for (const [v, tipo, c] of (sal.get(u) || [])) { if (en.has(v)) continue; ruta.push([u, v, tipo, c]); en.add(v); dfs(v); ruta.pop(); en.delete(v); }
    };
    dfs(s);
    cand.sort((a, b) => (a.filter(p => p[2] === -1).length - b.filter(p => p[2] === -1).length) || (a.length - b.length));
    return cand;
  }
  simular(flujo, camino) {
    const d = Math.min(...camino.map(p => p[3])); const n = new Map(flujo);
    for (const [u, v, t] of camino) { if (t === 1) n.set(K(u, v), n.get(K(u, v)) + d); else n.set(K(v, u), n.get(K(v, u)) - d); }
    return [n, d];
  }
  caminoConInverso(s, t, flujo, falta, estricto = false) {
    const cands = this.caminosResiduales(s, t, flujo);
    for (let k = 0; k < cands.length; k++) {
      if (k >= (estricto ? 40 : 250)) break;
      const [n, d] = this.simular(flujo, cands[k]);
      if (d + Grafo.maxDirecto(this.libres(n, false), s, t) >= falta) return cands[k];
    }
    if (estricto) return null;
    const dir = this.caminosDirectos(s, t, this.libres(flujo)).next().value;
    if (dir) { const l = this.libres(flujo); return dir.map(([u, v]) => [u, v, 1, l.get(K(u, v))]); }
    return cands[0] || null;
  }
  seCompleta(s, t, flujo, falta) {
    if (Grafo.maxDirecto(this.libres(flujo, false), s, t) >= falta) return 0;
    if (this.caminoConInverso(s, t, flujo, falta, true)) return 1;
    return null;
  }
  elegirCamino(s, t, flujo, falta) {
    const libres = this.libres(flujo); let desc = null, k = 0;
    for (const ruta of this.caminosDirectos(s, t, libres)) {
      if (k++ >= 600) break;
      const d = Math.min(...ruta.map(([u, v]) => libres.get(K(u, v))));
      const desp = new Map(libres); for (const [u, v] of ruta) desp.set(K(u, v), desp.get(K(u, v)) - d);
      if (d + Grafo.maxDirecto(desp, s, t) >= falta) return [ruta.map(([u, v]) => [u, v, 1, libres.get(K(u, v))]), desc];
      if (!desc) desc = { ruta, aumento: d };
    }
    return [this.caminoConInverso(s, t, flujo, falta), desc];
  }
  caminoClase(s, t, flujo, falta) {
    const libres = this.libres(flujo); let desc = null, k = 0;
    for (const ruta of this.caminosDirectos(s, t, libres)) {
      if (k++ >= 300) break;
      const d = Math.min(...ruta.map(([u, v]) => libres.get(K(u, v))));
      const n = new Map(flujo); for (const [u, v] of ruta) n.set(K(u, v), n.get(K(u, v)) + d);
      if (this.seCompleta(s, t, n, falta - d) !== null) return [ruta.map(([u, v]) => [u, v, 1, libres.get(K(u, v))]), desc];
      if (!desc) desc = { ruta, aumento: d, motivo: "varios" };
    }
    return [this.caminoConInverso(s, t, flujo, falta), desc];
  }

  /* ---- ejecución paso a paso ---- */
  preparar(evitar) {
    if (!this.cap.size) throw new Error("Agrega al menos una arista antes de calcular.");
    this.reiniciar();
    this.fuente = this.tf; this.sumidero = this.ts; this.evitar = evitar;
    this._f = new Map(); for (const k of this.cap.keys()) this._f.set(k, 0);
    this._total = 0; this._it = 0;
    this.objetivo = Grafo.maxDirecto(new Map(this.cap), this.fuente, this.sumidero);
    this.guardar("inicial");
  }
  guardar(fase, camino = [], aumento = 0, residuales = [], it = 0, cambios = []) {
    this.hist.push({ fase, flujo: new Map(this._f), total: this._total, camino, aumento, residuales, it, cambios, descartado: null });
  }
  aplicar(camino, desc = null) {
    const it = ++this._it; const ruta = camino.map(([u, v, t]) => [u, v, t]); const res = camino.map(p => p[3]);
    const d = Math.min(...res);
    this.guardar("camino", ruta, d, res, it); this.hist[this.hist.length - 1].descartado = desc;
    const cambios = [];
    for (const [u, v, t] of camino) { const k = t === 1 ? K(u, v) : K(v, u); const a = this._f.get(k); this._f.set(k, t === 1 ? a + d : a - d); cambios.push([KU(k), KV(k), a, this._f.get(k)]); }
    this._total += d;
    this.guardar("aumento", ruta, d, res, it, cambios);
    this.caminos.push({ it, camino: ruta, aumento: d, total: this._total, negativo: ruta.some(p => p[2] === -1) });
  }
  siguienteAutomatico() {
    const falta = this.objetivo - this._total; if (falta <= 0) return [null, null];
    if (this.evitar || this.caminos.some(c => c.negativo)) return this.elegirCamino(this.fuente, this.sumidero, this._f, falta);
    return this.caminoClase(this.fuente, this.sumidero, this._f, falta);
  }
  terminar() {
    this.guardar("final"); this.flujo = new Map(this._f); this.flujoMax = this._total;
    const alc = new Set([this.fuente]), cola = [this.fuente];
    while (cola.length) { const u = cola.shift();
      for (const [a, b, c] of this.aristas()) { const f = this.flujo.get(K(a, b));
        if (a === u && c > f && !alc.has(b)) { alc.add(b); cola.push(b); }
        if (b === u && f > 0 && !alc.has(a)) { alc.add(a); cola.push(a); } } }
    this.corte = this.describirCorte(alc);
  }
  ejecutar(evitar = false) {
    this.preparar(evitar);
    for (;;) { const [c, d] = this.siguienteAutomatico(); if (!c) break; this.aplicar(c, d); }
    this.terminar(); return this.flujoMax;
  }
  describirCorte(S) {
    S = new Set(S); const ida = [], vuelta = [];
    for (const [u, v] of this.aristas()) { if (S.has(u) && !S.has(v)) ida.push([u, v]); if (!S.has(u) && S.has(v)) vuelta.push([u, v]); }
    const fl = k => (this.flujo.get(k) || 0);
    const c = { S: [...S].sort((a, b) => a - b), T: [...Array(this.n).keys()].filter(x => !S.has(x)), ida, vuelta,
      capacidad: ida.reduce((a, [u, v]) => a + this.cap.get(K(u, v)), 0),
      neto: ida.reduce((a, [u, v]) => a + fl(K(u, v)), 0) - vuelta.reduce((a, [u, v]) => a + fl(K(u, v)), 0),
      infinito: ida.some(([u, v]) => this.esF(u, v)) };
    c.minimo = !c.infinito && c.capacidad === this.flujoMax; return c;
  }
  etiquetasCamino(camino, res) {
    const et = new Map(); if (!camino.length) return et; let d = null;
    et.set(camino[0][0], ["−", null]);
    camino.forEach(([u, v, t], i) => { const lim = (t === 1 && this.esF(u, v)) ? null : res[i];
      d = d === null ? lim : (lim === null ? d : Math.min(d, lim));
      et.set(v, [this.nombre(u) + (t === 1 ? "⁺" : "⁻"), d]); });
    return et;
  }
  /* ---- modo práctica ---- */
  terminado() { return this._total >= this.objetivo; }
  arcoLibre(x, y) {
    const k = K(x, y), r = K(y, x);
    if (this.cap.has(k)) { const l = this.cap.get(k) - this._f.get(k); if (l > 0) return [1, l]; }
    if (this.cap.has(r) && this._f.get(r) > 0) return [-1, this._f.get(r)];
    return null;
  }
  hayDirecto() { return !this.caminosDirectos(this.fuente, this.sumidero, this.libres(this._f)).next().done; }
  deshacerUltimo() {
    if (!this.caminos.length) return false;
    if (this.hist[this.hist.length - 1].fase === "final") { this.hist.pop(); this.corte = null; this.flujoMax = 0; }
    this.hist.splice(-2, 2); this.caminos.pop();
    const a = this.hist[this.hist.length - 1]; this._f = new Map(a.flujo); this._total = a.total; this._it--;
    return true;
  }
  aplicarInteractivo(camino) { this.aplicar(camino); if (this.terminado()) this.terminar(); }
  copia() {
    const g = new Grafo(this.n0); for (const [u, v, c] of this.originales()) g.agregar(u, v, c);
    g.definirTerminales(this.fuentes, this.sumideros); return g;
  }
}

/* ---- redes de ejemplo y aleatorias ---- */
function ejemplo7() {
  const g = new Grafo(7);
  [[1,2,16],[1,3,13],[2,4,12],[2,5,4],[3,4,6],[3,5,10],[4,6,14],[5,6,9],[5,7,4],[6,7,19]].forEach(([u,v,c]) => g.agregar(u-1, v-1, c));
  return g;
}
function ejemploMulti() {
  const g = new Grafo(8);
  [[1,3,10],[1,4,8],[2,4,7],[2,5,9],[3,6,6],[3,7,5],[4,6,9],[4,7,4],[5,6,5],[5,8,6],[6,7,8],[6,8,10]].forEach(([u,v,c]) => g.agregar(u-1, v-1, c));
  g.definirTerminales([0, 1], [6, 7]); return g;
}
function aleatorio(n, cmin = 5, cmax = 30) {
  const R = (a, b) => a + Math.floor(Math.random() * (b - a + 1)), pick = a => a[Math.floor(Math.random() * a.length)];
  const g = new Grafo(n), F = [0], Sm = [n - 1], I = []; for (let i = 1; i < n - 1; i++) I.push(i);
  const cap = () => R(cmin, cmax);
  for (const s of F) g.agregar(s, pick(I), cap());
  for (const v of I) if (!g.entrantes(v).length) g.agregar(pick([...F, ...I.filter(x => x < v)]), v, cap());
  for (const u of I) if (!g.vecinos(u).length) g.agregar(u, pick([...I.filter(x => x > u), ...Sm]), cap());
  for (const t of Sm) if (!g.entrantes(t).length) g.agregar(pick(I), t, cap());
  const pos = []; for (let u = 0; u < n; u++) for (let v = u + 1; v < n; v++) if (!Sm.includes(u) && !F.includes(v) && !(F.includes(u) && Sm.includes(v)) && !g.cap.has(K(u, v))) pos.push([u, v]);
  for (let i = pos.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [pos[i], pos[j]] = [pos[j], pos[i]]; }
  const rest = Math.max(0, Math.round(1.7 * n) - g.cap.size);
  for (const [u, v] of pos.slice(0, rest)) g.agregar(u, v, cap());
  g.definirTerminales(F, Sm); return g;
}

/* =========================================================
   ESTADO DE LA APLICACIÓN
   ========================================================= */
const $ = id => document.getElementById(id);
const st = {
  G: null, principal: null, alt: null, pestana: "principal", pasoTab: { principal: 0, alternativa: 0 },
  paso: 0, vista: "Red original", nombre: "", editar: false, origen: null, sel: null, mover: null,
  layout: null, fa: 1, fh: 1, zoom: 1, undo: [], guardados: [],
  practica: false, cam: [], listo: false, intentos: 0, nivelPista: 0, pistaArista: null, sugerencia: null, respuestas: {},
  anim: null, drag: null,
};
try { st.guardados = JSON.parse(localStorage.getItem("flujo-grafos") || "[]"); } catch (e) { st.guardados = []; }

const G = () => st.G;
const nom = x => st.G.nombre(x);
function estado(t) { $("status").textContent = t; }
function textoCamino(ruta) {
  if (!ruta.length) return "—";
  let s = nom(ruta[0][0]);
  for (const [, v, t] of ruta) s += (t === 1 ? " → " : " ⇢ ") + nom(v) + (t === -1 ? "⁻" : "");
  return s;
}
function pasoActual() {
  const g = G();
  if (g.hist.length) return g.hist[st.paso];
  return { fase: "sin ejecutar", flujo: g.flujo, total: 0, camino: [], aumento: 0, residuales: [], it: 0, cambios: [] };
}
function construyendo() {
  const g = G();
  return !!(st.practica && g.hist.length && st.paso === g.hist.length - 1 && g.hist[g.hist.length - 1].fase !== "final");
}
function capturar() { const g = G(); return { n: g.n0, aristas: g.originales(), f: [...g.fuentes], s: [...g.sumideros] }; }
function reconstruir(f) { const g = new Grafo(f.n); for (const [u, v, c] of f.aristas) g.agregar(u, v, c); try { g.definirTerminales(f.f, f.s); } catch (e) {} return g; }
function guardarUndo() { st.undo.push(capturar()); if (st.undo.length > 60) st.undo.shift(); }

/* ---- asignar una red nueva ---- */
function asignar(g, nombre, msg) {
  quitarPestanas();
  st.G = g; st.principal = g; st.nombre = nombre; st.origen = null; st.sel = null; st.mover = null;
  st.layout = null; st.undo = []; st.practica = $("modo").value === "practica" && false;
  $("n").value = g.n0;
  redCambiada(msg || `${nombre}. Revisa fuentes y sumideros y pulsa Calcular flujo.`, false);
}
function redCambiada(msg, relayout = true) {
  quitarPestanas(); st.principal = st.G;
  st.practica = false;
  if (relayout) { if ($("autoOrden").checked) reordenar(); }
  if (st.sel && !G().cap.has(K(...st.sel))) st.sel = null;
  st.paso = 0; st.vista = "Red original"; $("vista").value = st.vista;
  estado(msg); actualizarTerminales(); render();
}
function actualizarTerminales() {
  const g = G(), f = g.fuentes.map(letra).join(", "), s = g.sumideros.map(letra).join(", ");
  $("bFuentes").textContent = (g.fuentes.length > 1 ? "Fuentes: " : "Fuente: ") + f + (g.S !== null ? " (S)" : "");
  $("bSumideros").textContent = (g.sumideros.length > 1 ? "Sumideros: " : "Sumidero: ") + s + (g.T !== null ? " (T)" : "");
}
function textoTerminales() {
  const g = G(); let f = g.fuentes.map(letra).join(", "), s = g.sumideros.map(letra).join(", ");
  if (g.S !== null) f = `S → {${f}}`; if (g.T !== null) s = `{${s}} → T`;
  return `Fuente: ${f}   Sumidero: ${s}`;
}

/* ---- pestañas Con / Sin flujo negativo ---- */
function quitarPestanas() {
  if (st.pestana === "alternativa" && st.principal) { st.G = st.principal; }
  st.alt = null; st.pestana = "principal"; st.pasoTab = { principal: 0, alternativa: 0 };
  $("pestanas").hidden = true; $("tabCon").setAttribute("aria-pressed", "true"); $("tabSin").setAttribute("aria-pressed", "false");
}
function aPrincipal() { if (st.pestana === "alternativa") cambiarPestana("principal"); }
function crearPestanas() {
  const p = st.principal; if (!p.caminos.some(c => c.negativo)) return;
  const c = p.copia(); c.ejecutar(true); st.alt = c; $("pestanas").hidden = false;
}
function cambiarPestana(nombre) {
  if (nombre === st.pestana || (nombre === "alternativa" && !st.alt)) return;
  st.pasoTab[st.pestana] = st.paso; st.pestana = nombre;
  st.G = nombre === "alternativa" ? st.alt : st.principal;
  $("tabCon").setAttribute("aria-pressed", String(nombre === "principal"));
  $("tabSin").setAttribute("aria-pressed", String(nombre === "alternativa"));
  st.sel = null; st.origen = null; if (nombre === "alternativa") setEditar(false);
  irPaso(st.pasoTab[nombre]);
  estado(nombre === "alternativa"
    ? `Sin flujo negativo: el mismo grafo resuelto eligiendo caminos que no necesitan devolver flujo. Llega al mismo máximo (${G().flujoMax}). Esta pestaña es solo para ver.`
    : "Con flujo negativo: la solución siguiendo los caminos en orden.");
}

/* ---- calcular ---- */
function calcular() {
  quitarPestanas();
  if ($("modo").value === "practica") { iniciarPractica(); return; }
  st.practica = false;
  const g = G();
  try { g.ejecutar(false); } catch (e) { mensaje("No se pudo calcular", e.message); return; }
  st.paso = 0; st.origen = null; st.sel = null; st.vista = "Red original"; $("vista").value = st.vista;
  st.principal = g; crearPestanas();
  let m = "Cálculo terminado. Usa Siguiente para recorrer cada iteración o Resultado para ver el estado final.";
  if (g.caminos.some(c => c.negativo)) m += " Este cálculo usa flujo negativo: compáralo con la pestaña «Sin flujo negativo».";
  estado(m); render();
}
function irPaso(i) {
  const g = G(); if (!g.hist.length) return;
  st.paso = Math.max(0, Math.min(i, g.hist.length - 1));
  const fase = pasoActual().fase;
  st.vista = (fase === "camino" || construyendo()) ? "Red residual" : fase === "final" ? "Corte mínimo" : "Red original";
  $("vista").value = st.vista;
  const t = { inicial: "Estado inicial: todos los flujos en 0.", camino: "Se encontró un camino aumentante en la red residual; aún no cambian los flujos.",
    aumento: "Flujos actualizados con el cuello de botella del camino.", final: "No hay más caminos aumentantes: el flujo es máximo y lo certifica el corte mínimo." };
  if (!st.practica) estado(t[fase] || "");
  render();
}

/* =========================================================
   EDICIÓN DEL GRAFO
   ========================================================= */
function setEditar(on) { st.editar = on; $("editar").checked = on; $("tgEditar").classList.toggle("on", on); st.origen = null; if (!on) st.sel = null; }
function capacidadSugerida(u, v) {
  const g = G(); if (g.cap.has(K(u, v))) return g.cap.get(K(u, v));
  const cs = g.originales().map(a => a[2]).sort((a, b) => a - b); return cs.length ? cs[cs.length >> 1] : 10;
}
function conectar(u, v) {
  const g = G(), existe = g.cap.has(K(u, v));
  pedirNumero(`Capacidad de ${nom(u)} → ${nom(v)}`, existe ? "La arista ya existe: escribe la nueva capacidad o elimínala." : "Escribe la capacidad de la arista (entero mayor que 0).",
    capacidadSugerida(u, v), existe ? [["Eliminar", () => eliminarArista(u, v)]] : [], c => {
      guardarUndo();
      try { g.agregar(u, v, c, existe); } catch (e) { st.undo.pop(); mensaje("Arista rechazada", e.message); return; }
      redCambiada(`Arista ${nom(u)} → ${nom(v)} con capacidad ${c}. Sigue tocando vértices para agregar más.`);
    });
}
function eliminarArista(u, v) {
  const g = G(); if (!g.cap.has(K(u, v))) return; guardarUndo();
  try { g.eliminar(u, v); } catch (e) { st.undo.pop(); mensaje("No se eliminó", e.message); return; }
  st.sel = null; redCambiada(`Arista ${nom(u)} → ${nom(v)} eliminada (Deshacer la recupera).`);
}
function moverArista(u, v, nu, nv) {
  const g = G(); if (u === nu && v === nv) return;
  if (g.cap.has(K(nu, nv))) { mensaje("No se cambió", `Ya existe la arista ${nom(nu)} → ${nom(nv)}.`); return; }
  const c = g.cap.get(K(u, v)); guardarUndo(); g.eliminar(u, v);
  try { g.agregar(nu, nv, c); } catch (e) { g.agregar(u, v, c); st.undo.pop(); mensaje("No se cambió", e.message); render(); return; }
  st.sel = [nu, nv];
  redCambiada(`Arista ${nom(u)} → ${nom(v)} cambiada a ${nom(nu)} → ${nom(nv)}; la capacidad ${c} se mantiene.`);
}
function invertirArista(u, v) {
  const g = G(), c = g.cap.get(K(u, v)); guardarUndo(); g.eliminar(u, v);
  try { g.agregar(v, u, c); } catch (e) { g.agregar(u, v, c); st.undo.pop(); mensaje("No se puede invertir", e.message); render(); return; }
  st.sel = [v, u]; redCambiada(`Arista invertida: ahora va de ${nom(v)} a ${nom(u)}.`);
}
function hojaArista(u, v) {
  const g = G();
  if (g.esF(u, v)) { estado(`${nom(u)} → ${nom(v)} es una arista ficticia (∞): se quita desde Fuentes y sumideros.`); return; }
  st.sel = [u, v]; render();
  modal(`Arista ${nom(u)} → ${nom(v)}`, `<p>Capacidad actual: <b>${g.cap.get(K(u, v))}</b>. Cambiar origen o destino conserva la capacidad.</p>
    <label for="capNueva" style="font-weight:700">Nueva capacidad</label> <input id="capNueva" type="number" min="1" value="${g.cap.get(K(u, v))}">`,
    [["Eliminar", () => eliminarArista(u, v), "danger"],
     ["Invertir sentido", () => invertirArista(u, v)],
     ["Cambiar origen", () => { st.mover = { tipo: "origen", e: [u, v] }; estado(`Toca el nuevo origen para ${nom(u)} → ${nom(v)}.`); }],
     ["Cambiar destino", () => { st.mover = { tipo: "destino", e: [u, v] }; estado(`Toca el nuevo destino para ${nom(u)} → ${nom(v)}.`); }],
     ["Guardar capacidad", () => {
        const c = parseInt($("capNueva").value, 10); if (!(c > 0)) return false;
        guardarUndo(); g.agregar(u, v, c, true); redCambiada(`Capacidad de ${nom(u)} → ${nom(v)} cambiada a ${c}.`);
      }, "primary"]]);
}
function deshacer() {
  aPrincipal();
  if (!st.undo.length) { estado("No hay cambios para deshacer."); return; }
  const f = st.undo.pop(); st.G = reconstruir(f); st.origen = null; st.sel = null; $("n").value = f.n;
  redCambiada("Último cambio deshecho.");
}
function nuevoManual(n) {
  aPrincipal();
  n = Math.min(16, Math.max(7, n | 0 || 7)); $("n").value = n;
  const antes = st.G ? capturar() : null;
  asignar(new Grafo(n), "Grafo manual", `${n} vértices sin aristas (a – ${letra(n - 1)}). Toca un vértice y luego otro para conectarlos.`);
  if (antes) st.undo.push(antes);
  setEditar(true); render();
}
function limpiar() {
  aPrincipal();
  if (!G().originales().length) return;
  modal("Limpiar", "<p>¿Borrar todas las aristas del grafo? Puedes recuperarlas con Deshacer.</p>", [["Borrar aristas", () => {
    const antes = capturar(); asignar(new Grafo(G().n0), "Grafo manual", "Aristas eliminadas. Activa «Conectar con clic» para agregar nuevas.");
    st.undo.push(antes); render();
  }, "danger"]]);
}

/* =========================================================
   DISTRIBUCIÓN DE LOS NODOS
   ========================================================= */
function layoutAuto() {
  const g = G(), sx = 170 * st.fa, py = 120 * st.fh, pos = {};
  const prev = st.layout || {};
  if (!g.cap.size) {
    const col = Math.min(5, Math.max(3, Math.ceil(Math.sqrt(g.n * 1.5)))), fil = Math.ceil(g.n / col), px = 130 * st.fa;
    const W = Math.max(640, col * px + 80), H = Math.max(380, fil * py + 100);
    for (let x = 0; x < g.n; x++) { const f = Math.floor(x / col), c = x % col, cant = Math.min(col, g.n - f * col);
      pos[g.nombre(x)] = { x: W / 2 + (c - (cant - 1) / 2) * px, y: H / 2 + (f - (fil - 1) / 2) * py }; }
    return pos;
  }
  const con = new Set(); for (const k of g.cap.keys()) { con.add(KU(k)); con.add(KV(k)); }
  const aisl = []; for (let x = 0; x < g.n; x++) if (!con.has(x)) aisl.push(x);
  const niv = {}; for (const x of con) niv[x] = 0;
  for (const u of g.ordenTopo()) if (con.has(u)) for (const v of g.vecinos(u)) niv[v] = Math.max(niv[v], niv[u] + 1);
  const orig = [...con].filter(x => x < g.n0);
  if (orig.length) {
    const ult = Math.max(...orig.map(x => niv[x]));
    for (const x of g.sumideros) if (con.has(x) && !g.salidasOrig(x).length) niv[x] = ult;
    if (g.T !== null && con.has(g.T)) niv[g.T] = 1 + Math.max(...g.entrantes(g.T).map(p => niv[p]));
  }
  const antes = x => { const p = prev[g.nombre(x)]; return p ? p.y * 100 + x : 1e9 + x; };
  let orden = {}; for (const x of con) (orden[niv[x]] = orden[niv[x]] || []).push(x);
  for (const k in orden) orden[k].sort((a, b) => antes(a) - antes(b));
  const aristas = [...g.cap.keys()].map(k => [KU(k), KV(k)]);
  const niveles = Object.keys(orden).map(Number).sort((a, b) => a - b);
  const puntaje = o => {
    const p = {}; for (const k in o) o[k].forEach((x, i) => p[x] = [k * 1.6, i - (o[k].length - 1) / 2]);
    const lado = (a, b, c) => (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]);
    let tot = 0; const seg = aristas.map(([u, v]) => [p[u], p[v], u, v]);
    for (let i = 0; i < seg.length; i++) { const [p1, p2, a, b] = seg[i];
      for (let j = i + 1; j < seg.length; j++) { const [p3, p4, c, d] = seg[j];
        if (new Set([a, b, c, d]).size < 4) continue;
        if (lado(p1, p2, p3) * lado(p1, p2, p4) < 0 && lado(p3, p4, p1) * lado(p3, p4, p2) < 0) tot++; }
      const dx = p2[0] - p1[0], dy = p2[1] - p1[1], l = dx * dx + dy * dy || 1;
      for (const w in p) { const q = p[w]; if (+w === a || +w === b) continue;
        const t = ((q[0] - p1[0]) * dx + (q[1] - p1[1]) * dy) / l;
        if (t > .05 && t < .95 && Math.hypot(q[0] - (p1[0] + t * dx), q[1] - (p1[1] + t * dy)) < .4) tot++; } }
    return tot;
  };
  const clon = o => { const r = {}; for (const k in o) r[k] = o[k].slice(); return r; };
  let mejor = clon(orden), mejorP = puntaje(mejor);
  for (let b = 0; b < 6; b++) {
    const der = b % 2 === 0, sec = der ? niveles.slice(1) : niveles.slice(0, -1).reverse();
    for (const nv of sec) {
      const rango = {}; for (const k in orden) orden[k].forEach((x, i) => rango[x] = i / Math.max(1, orden[k].length - 1));
      const clave = x => { const vs = (der ? g.entrantes(x) : g.vecinos(x)).filter(y => y in rango);
        return vs.length ? vs.reduce((a, y) => a + rango[y], 0) / vs.length : rango[x]; };
      orden[nv].sort((a, c) => (clave(a) - clave(c)) || (antes(a) - antes(c)));
    }
    const p = puntaje(orden); if (p < mejorP) { mejor = clon(orden); mejorP = p; }
  }
  orden = clon(mejor);
  for (let vuelta = 0, mejora = true; mejora && vuelta < 30; vuelta++) { mejora = false;
    for (const nv of niveles) { const ns = orden[nv];
      for (let i = 0; i + 1 < ns.length; i++) { [ns[i], ns[i + 1]] = [ns[i + 1], ns[i]]; const p = puntaje(orden);
        if (p < mejorP) { mejorP = p; mejora = true; } else [ns[i], ns[i + 1]] = [ns[i + 1], ns[i]]; } } }
  const ult = Math.max(...niveles), alta = Math.max(...niveles.map(k => orden[k].length));
  const fila = aisl.length ? py * 1.25 : 0;
  const W = Math.max(640, 170 + sx * ult, 170 + 110 * st.fa * Math.max(0, aisl.length - 1));
  const H = Math.max(380, 170 + py * (alta - 1) + fila), Hc = H - fila;
  for (const nv of niveles) { const ns = orden[nv]; const x = ult ? 85 + (W - 170) * nv / ult : W / 2;
    const sep = Math.min(155 * st.fh, (Hc - 180) / Math.max(1, ns.length - 1));
    ns.forEach((n, i) => pos[g.nombre(n)] = { x, y: Hc / 2 + (i - (ns.length - 1) / 2) * sep }); }
  aisl.forEach((n, i) => pos[g.nombre(n)] = { x: 85 + 110 * st.fa * i, y: H - 70 });
  return pos;
}
function layoutCompleto() {
  const g = G(); if (!st.layout) st.layout = layoutAuto();
  const L = st.layout;
  for (let x = 0; x < g.n; x++) {
    const nm = g.nombre(x); if (L[nm]) continue;
    let ref, dx;
    if (x === g.S) { ref = g.fuentes.map(letra).filter(k => L[k]).map(k => L[k]); dx = -150; }
    else if (x === g.T) { ref = g.sumideros.map(letra).filter(k => L[k]).map(k => L[k]); dx = 150; }
    if (!ref || !ref.length) { st.layout = layoutAuto(); return layoutCompleto(); }
    L[nm] = { x: (dx < 0 ? Math.min(...ref.map(p => p.x)) : Math.max(...ref.map(p => p.x))) + dx, y: ref.reduce((a, p) => a + p.y, 0) / ref.length };
  }
  const xs = Object.values(L).map(p => p.x), ys = Object.values(L).map(p => p.y);
  const dx = Math.max(0, 78 - Math.min(...xs)), dy = Math.max(0, 70 - Math.min(...ys));
  if (dx || dy) for (const k in L) { L[k] = { x: L[k].x + dx, y: L[k].y + dy }; }
  const pos = {}; for (let x = 0; x < g.n; x++) pos[x] = L[g.nombre(x)];
  return pos;
}
function reordenar() {
  const desde = st.layout ? { ...st.layout } : null;
  const destino = layoutAuto();
  st.layout = destino;
  if (!desde || matchMedia("(prefers-reduced-motion: reduce)").matches) return;
  const inicio = {}; for (const k in destino) inicio[k] = desde[k] || destino[k];
  if (st.anim) cancelAnimationFrame(st.anim);
  const t0 = performance.now(), dur = 260;
  const frame = now => { let t = Math.min(1, (now - t0) / dur); t = 1 - Math.pow(1 - t, 3);
    const L = {}; for (const k in destino) L[k] = { x: inicio[k].x + (destino[k].x - inicio[k].x) * t, y: inicio[k].y + (destino[k].y - inicio[k].y) * t };
    st.layout = L; dibujar(); if (t < 1) st.anim = requestAnimationFrame(frame); else { st.layout = destino; st.anim = null; dibujar(); } };
  st.layout = inicio; st.anim = requestAnimationFrame(frame);
}
function escalar(fx, fy) {
  if (!st.layout) return; const L = st.layout, xs = Object.values(L).map(p => p.x), ys = Object.values(L).map(p => p.y);
  const x0 = Math.min(...xs), y0 = Math.min(...ys);
  for (const k in L) L[k] = { x: x0 + (L[k].x - x0) * fx, y: y0 + (L[k].y - y0) * fy };
}

/* =========================================================
   DIBUJO (SVG)
   ========================================================= */
const R = 26;
const medir = (() => { const c = document.createElement("canvas").getContext("2d"); return t => { c.font = "700 12px 'JetBrains Mono', monospace"; return c.measureText(t).width; }; })();
const esc = s => String(s).replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]);
let ultimaPos = {};

function dibujar() {
  const g = G(), svg = $("lienzo"); if (!g) return;
  const pos = layoutCompleto(); ultimaPos = pos;
  const xs = Object.values(pos).map(p => p.x), ys = Object.values(pos).map(p => p.y);
  const W = Math.max(600, Math.max(...xs) + 90), H = Math.max(360, Math.max(...ys) + 90);
  const ancho = $("wrap").clientWidth - 2 || 600;
  const ajuste = Math.max(0.62, Math.min(1, ancho / W)), z = ajuste * st.zoom;  // en celular no se encoge más: se desplaza con el dedo
  svg.setAttribute("viewBox", `0 0 ${W} ${H}`); svg.setAttribute("width", Math.round(W * z)); svg.setAttribute("height", Math.round(H * z));

  const paso = pasoActual(), fase = paso.fase, vista = st.vista, cons = construyendo();
  let cDir = new Set(paso.camino.filter(p => p[2] === 1).map(([u, v]) => K(u, v)));
  let cInv = new Set(paso.camino.filter(p => p[2] === -1).map(([u, v]) => K(v, u)));
  if (cons) { const r = rutaUsuario(); cDir = new Set(r.filter(p => p[2] === 1).map(([u, v]) => K(u, v))); cInv = new Set(r.filter(p => p[2] === -1).map(([u, v]) => K(v, u))); }
  const cambios = new Map(paso.cambios.map(([u, v, a, d]) => [K(u, v), [a, d]]));
  const corte = vista === "Corte mínimo" && g.corte ? g.describirCorte(g.corte.S) : null;
  const flujo = paso.flujo;

  let fondo = "", lineas = "", hits = "", flechas = "";
  const etiquetas = [], llenas = new Set();
  for (let gx = 14; gx < W; gx += 28) for (let gy = 14; gy < H; gy += 28) fondo += `<rect class="dots" x="${gx}" y="${gy}" width="1.4" height="1.4"/>`;

  function arista(u, v, label, color, grosor, opt = {}) {
    const { dash = false, inverso = false, extra = 0, superpuesta = false, edge = null } = opt;
    const p1 = pos[u], p2 = pos[v]; const x1 = p1.x, y1 = p1.y, x2 = p2.x, y2 = p2.y;
    const dx = x2 - x1, dy = y2 - y1, dist = Math.hypot(dx, dy) || 1;
    let curva = extra;
    if (!extra) { const hueco = R + 14; let nec = 0;
      for (const w in pos) { if (+w === u || +w === v) continue; const q = pos[w];
        const t = ((q.x - x1) * dx + (q.y - y1) * dy) / (dist * dist); if (!(t > .05 && t < .95)) continue;
        const d = ((q.x - x1) * -dy + (q.y - y1) * dx) / dist; if (Math.abs(d) >= hueco) continue;
        const falta = (hueco - Math.abs(d)) / (2 * t * (1 - t)); if (falta > Math.abs(nec)) nec = (d > 0 ? -1 : 1) * falta; }
      curva = Math.max(-220, Math.min(220, nec)); }
    const mx = (x1 + x2) / 2 - dy / dist * curva, my = (y1 + y2) / 2 + dx / dist * curva;
    const d1 = Math.hypot(mx - x1, my - y1) || 1, d2 = Math.hypot(x2 - mx, y2 - my) || 1;
    const sx = x1 + (R + 3) * (mx - x1) / d1, sy = y1 + (R + 3) * (my - y1) / d1;
    const ex = x2 - (R + 3) * (x2 - mx) / d2, ey = y2 - (R + 3) * (y2 - my) / d2;
    const camino = `M${sx.toFixed(1)} ${sy.toFixed(1)} Q${mx.toFixed(1)} ${my.toFixed(1)} ${ex.toFixed(1)} ${ey.toFixed(1)}`;
    if (edge && st.sel && st.sel[0] === edge[0] && st.sel[1] === edge[1] && !inverso) lineas += `<path class="selbg" d="${camino}" stroke-width="${grosor + 9}"/>`;
    lineas += `<path class="ln s-${color}" d="${camino}" stroke-width="${grosor}"${dash ? ' stroke-dasharray="7 5"' : ""}/>`;
    // punta de flecha
    const [px, py, tx, ty] = inverso ? [sx, sy, sx - mx, sy - my] : [ex, ey, ex - mx, ey - my];
    const tl = Math.hypot(tx, ty) || 1, ux = tx / tl, uy = ty / tl, L = 12, A = 5.5;
    flechas += `<polygon class="f-${color}" points="${px},${py} ${px - ux * L - uy * A},${py - uy * L + ux * A} ${px - ux * L + uy * A},${py - uy * L - ux * A}"/>`;
    if (superpuesta) return;
    if (edge) hits += `<path class="hit" d="${camino}" data-${inverso ? "ret" : "edge"}="${edge[0]},${edge[1]}"/>`;
    const cand = [.5, .36, .64, .27, .73, .2, .8].map(t => ({ x: (1 - t) ** 2 * sx + 2 * (1 - t) * t * mx + t * t * ex, y: (1 - t) ** 2 * sy + 2 * (1 - t) * t * my + t * t * ey }));
    etiquetas.push({ cand, label, color, edge, inverso });
  }

  const aristas = g.aristas();
  if (vista === "Red residual") {
    for (const [u, v, c] of aristas) {
      const f = flujo.get(K(u, v)), disp = c - f;
      if (disp === 0 && !g.esF(u, v)) llenas.add(K(u, v));
      let color = "resid", gr = 2.2;
      if (cDir.has(K(u, v))) { color = "path"; gr = 3.4; } else if (disp === 0) { color = "sat"; gr = 1.6; }
      arista(u, v, g.textoCap(u, v, disp), color, gr, { edge: [u, v] });
      if (f > 0 && cInv.has(K(u, v)))
        arista(u, v, cons ? "−?" : `devuelve ${paso.aumento} de ${nom(u)}→${nom(v)}`, "neg", 3.4, { dash: true, inverso: true, extra: 42, edge: [u, v] });
    }
  } else {
    for (const [u, v, c] of aristas) {
      const f = flujo.get(K(u, v)); let color = f ? "flow" : "idle", gr = f ? 2.6 : 1.9, dash = false;
      let texto = `${g.textoCap(u, v)}, ${f}`;
      if (f === c && !g.esF(u, v)) llenas.add(K(u, v));
      if (!corte) {
        if (cDir.has(K(u, v))) { color = "path"; gr = 3.4; }
        else if (cInv.has(K(u, v))) { color = "neg"; gr = 3.4; dash = true; }
        if (fase === "aumento" && cambios.has(K(u, v))) { const [a, d] = cambios.get(K(u, v)), df = d - a;
          texto = `${g.textoCap(u, v)}, ${a} ${df > 0 ? "+" : "−"} ${Math.abs(df)} = ${d}`; }
      } else {
        if (corte.ida.some(([a, b]) => a === u && b === v)) { color = "cut"; gr = 3.6; dash = true; }
        else if (corte.vuelta.some(([a, b]) => a === u && b === v)) { color = "neg"; gr = 2.4; dash = true; }
      }
      arista(u, v, texto, color, gr, { dash, edge: [u, v] });
    }
  }
  // práctica: flechas de regreso del vértice actual, pista y sugerencia
  if (cons && !st.listo) {
    const ult = st.cam[st.cam.length - 1];
    for (const [y, t, c] of opcionesDesde(ult)) if (t === -1) arista(y, ult, `devolver ≤${c}`, "neg", 2.4, { dash: true, inverso: true, extra: 42, edge: [y, ult] });
    if (st.pistaArista && st.pistaArista[1] !== ult) { const [a, b] = st.pistaArista; arista(a, b, "devolver aquí", "neg", 2.4, { dash: true, inverso: true, extra: 42, edge: [a, b] }); }
  }
  if (cons && st.sugerencia) for (const [u, v, t] of st.sugerencia) {
    if (t === 1) arista(u, v, "", "path", 5, { dash: true, superpuesta: true });
    else arista(v, u, "", "neg", 5, { dash: true, inverso: true, extra: 42, superpuesta: true });
  }

  // etiquetas sin superponerse
  let labs = ""; const ocupados = Object.values(pos).map(p => [p.x - R - 2, p.y - R - 2, p.x + R + 2, p.y + R + 2]);
  const choque = (a, b) => Math.max(0, Math.min(a[2], b[2]) - Math.max(a[0], b[0])) * Math.max(0, Math.min(a[3], b[3]) - Math.max(a[1], b[1]));
  for (const e of etiquetas) {
    const mw = medir(e.label) / 2 + 6, mh = 10; let mejor = null;
    for (const c of e.cand) { const caja = [c.x - mw, c.y - mh, c.x + mw, c.y + mh]; const tot = ocupados.reduce((a, o) => a + choque(caja, o), 0);
      if (!mejor || tot < mejor.tot) mejor = { tot, c, caja }; if (tot === 0) break; }
    ocupados.push(mejor.caja);
    const full = e.edge && !e.inverso && llenas.has(K(...e.edge));
    const data = e.edge ? ` data-${e.inverso ? "ret" : "edge"}="${e.edge[0]},${e.edge[1]}"` : "";
    labs += `<g${data} style="cursor:pointer"><rect class="lab s-${e.color}${full ? " full" : ""}" x="${mejor.caja[0]}" y="${mejor.caja[1]}" width="${mw * 2}" height="${mh * 2}" rx="4" stroke-width="1"/>`
      + `<text class="labt t-${e.color}" x="${mejor.c.x}" y="${mejor.c.y}">${esc(e.label)}</text></g>`;
  }

  // línea del corte
  let corteSvg = "";
  if (corte) corteSvg = lineaCorte(pos, new Set(corte.S), W, H);

  // nodos
  let nodos = "";
  for (let x = 0; x < g.n; x++) {
    const { x: cx, y: cy } = pos[x]; let fill = "var(--accent-soft)", stroke = "var(--accent)", tcol = "var(--accent)", rol = "", ancho = 2.5;
    if (x === g.S) { fill = "var(--src-dark)"; stroke = "var(--src-dark)"; tcol = "var(--surface)"; rol = "superfuente"; ancho = 3.5; }
    else if (x === g.T) { fill = "var(--sink-dark)"; stroke = "var(--sink-dark)"; tcol = "var(--surface)"; rol = "supersumidero"; ancho = 3.5; }
    else if (corte) { const enS = corte.S.includes(x); fill = enS ? "var(--src-fill)" : "var(--sink-fill)"; stroke = tcol = enS ? "var(--src)" : "var(--sink)"; }
    else if (g.fuentes.includes(x)) { fill = "var(--src-fill)"; stroke = tcol = "var(--src)"; }
    else if (g.sumideros.includes(x)) { fill = "var(--sink-fill)"; stroke = tcol = "var(--sink)"; }
    if (x !== g.S && x !== g.T) { if (g.fuentes.includes(x)) { rol = "fuente"; ancho = 3.5; } else if (g.sumideros.includes(x)) { rol = "sumidero"; ancho = 3.5; } }
    nodos += `<g class="nodo" data-node="${x}"><circle cx="${cx + 3}" cy="${cy + 4}" r="${R}" fill="var(--shadow)"/>`
      + `<circle cx="${cx}" cy="${cy}" r="${R}" fill="${fill}" stroke="${stroke}" stroke-width="${ancho}"/>`
      + `<text x="${cx}" y="${cy}" fill="${tcol}">${nom(x)}</text>`
      + (rol ? `<text class="rol" x="${cx}" y="${cy + R + 14}" fill="${x === g.S || x === g.T ? fill : stroke}">${rol}</text>` : "") + `</g>`;
  }
  // etiquetas (anterior, Δ) del camino
  if (fase === "camino" && !corte && !cons) {
    for (const [x, [ant, d]] of g.etiquetasCamino(paso.camino, paso.residuales)) {
      const t = `(${ant}, ${d === null ? INF : d})`, w = medir(t) / 2 + 5, { x: cx, y: cy } = pos[x], neg = ant.endsWith("⁻");
      nodos += `<rect class="lab s-${neg ? "neg" : "path"}" x="${cx - w}" y="${cy - R - 24}" width="${w * 2}" height="18" rx="4"/><text class="vlab t-${neg ? "neg" : "path"}" x="${cx}" y="${cy - R - 15}">${esc(t)}</text>`;
    }
  }
  // anillos: origen al conectar, práctica
  let anillos = "";
  const anillo = (x, cls, dash) => { const { x: cx, y: cy } = pos[x]; anillos += `<circle class="ln ${cls}" cx="${cx}" cy="${cy}" r="${R + 7}" stroke-width="3"${dash ? ' stroke-dasharray="5 3"' : ""}/>`; };
  if (st.origen !== null && pos[st.origen]) anillo(st.origen, "s-path", true);
  if (cons && st.cam.length) { anillo(st.cam[st.cam.length - 1], "s-path", false);
    if (!st.listo) for (const [y, t] of opcionesDesde(st.cam[st.cam.length - 1])) anillo(y, t === -1 ? "s-neg" : "s-resid", true); }
  const vacio = !g.cap.size ? `<text x="${W / 2}" y="30" text-anchor="middle" fill="var(--muted)" style="font-size:14px">Activa «Conectar con clic» y toca dos vértices para crear una arista.</text>` : "";
  svg.innerHTML = fondo + corteSvg + lineas + flechas + hits + labs + anillos + nodos + vacio;

  // subtítulo
  let sub = "Etiqueta de cada arco: capacidad, flujo";
  if (vista === "Red residual") sub = "Red residual: c − f (lo que aún cabe) · magenta = flujo negativo aplicado";
  else if (corte) sub = "Corte mínimo (S, T) · la línea roja separa S (verde) de T (rojo)";
  else if (st.editar) sub = "Conectar: toca el origen y luego el destino · toca una arista para editarla · arrastra un nodo para moverlo";
  if (cons) sub = "Práctica: arma el camino tocando los vértices; toca el último para retroceder";
  $("sub").textContent = sub;
}
function lineaCorte(pos, S, W, H) {
  const sN = [], tN = []; for (const k in pos) (S.has(+k) ? sN : tN).push([pos[k].x, pos[k].y]);
  if (!sN.length || !tN.length) return "";
  let mejor = null;
  for (let gr = 0; gr < 180; gr++) { const a = gr * Math.PI / 180, nx = Math.cos(a), ny = Math.sin(a);
    const ps = sN.map(([x, y]) => x * nx + y * ny), pt = tN.map(([x, y]) => x * nx + y * ny);
    for (const sg of [1, -1]) { const hueco = sg === 1 ? Math.min(...pt) - Math.max(...ps) : Math.min(...ps) - Math.max(...pt);
      if (hueco <= 0) continue; const cen = sg === 1 ? (Math.min(...pt) + Math.max(...ps)) / 2 : (Math.min(...ps) + Math.max(...pt)) / 2;
      const p = hueco - .15 * Math.min(gr, 180 - gr); if (!mejor || p > mejor[0]) mejor = [p, nx, ny, cen, sg]; } }
  if (!mejor) return "";
  const [, nx, ny, cen, sg] = mejor, ext = [];
  for (const x of [0, W]) if (Math.abs(ny) > 1e-9) { const y = (cen - nx * x) / ny; if (y >= -1 && y <= H + 1) ext.push([x, y]); }
  for (const y of [0, H]) if (Math.abs(nx) > 1e-9) { const x = (cen - ny * y) / nx; if (x >= -1 && x <= W + 1) ext.push([x, y]); }
  if (ext.length < 2) return "";
  ext.sort((a, b) => a[1] - b[1] || a[0] - b[0]);
  const [x1, y1] = ext[0], [x2, y2] = ext[ext.length - 1], l = Math.hypot(x2 - x1, y2 - y1) || 1;
  const bx = x1 + (x2 - x1) * 26 / l, by = y1 + (y2 - y1) * 26 / l, ls = -sg;
  return `<line class="cutline" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}"/>`
    + `<text x="${bx + nx * 18 * ls}" y="${by + ny * 18 * ls}" fill="var(--src)" style="font:italic 800 18px var(--f-display)" text-anchor="middle">S</text>`
    + `<text x="${bx - nx * 18 * ls}" y="${by - ny * 18 * ls}" fill="var(--sink)" style="font:italic 800 18px var(--f-display)" text-anchor="middle">T</text>`;
}

/* =========================================================
   PANELES
   ========================================================= */
function render() {
  const g = G(); if (!g) return;
  dibujar(); paneles(); explicacion(); evolucion(); controlesPractica();
  const total = Math.max(0, g.hist.length - 1);
  $("paso").textContent = `Paso ${st.paso} / ${total}`;
  const h = g.hist.length > 0;
  $("bInicio").disabled = $("bAnterior").disabled = !(h && st.paso > 0);
  $("bSiguiente").disabled = $("bResultado").disabled = !(h && st.paso < total);
}
function paneles() {
  const g = G(), p = pasoActual();
  $("mFlujo").textContent = p.total;
  let d;
  if (g.hist.length) {
    if (construyendo()) d = `Práctica · iteración ${g.caminos.length + 1}: elige un camino\n`;
    else if (p.fase === "camino") d = `Iteración ${p.it}: se sumarán +${p.aumento} → ${p.total + p.aumento}\n`;
    else if (p.fase === "aumento") d = `Iteración ${p.it}: ${p.total - p.aumento} + ${p.aumento} = ${p.total}\n`;
    else d = `Máximo calculado: ${g.flujoMax}\n`;
    d += textoTerminales();
  } else d = "Pulsa Calcular flujo para comenzar.\n" + textoTerminales();
  $("dFlujo").textContent = d;
  const c = g.corte;
  $("mCorte").textContent = c ? c.capacidad : "Pendiente";
  $("dCorte").textContent = c ? `Aristas: ${c.ida.map(([u, v]) => `(${nom(u)}, ${nom(v)})`).join(", ")}\n|f| = ${g.flujoMax} = c(S, T) = ${c.capacidad} ✓` : "Se obtiene al terminar el algoritmo y certifica que el flujo es máximo.";
  const sale = g.originales().filter(([u]) => g.fuentes.includes(u)).reduce((a, x) => a + x[2], 0);
  const entra = g.originales().filter(([, v]) => g.sumideros.includes(v)).reduce((a, x) => a + x[2], 0);
  if (g.originales().length) { $("mLim").textContent = "≤ " + Math.min(sale, entra);
    $("dLim").textContent = `Sale de las fuentes: ${sale} · Entra a los sumideros: ${entra}\nEl flujo máximo no puede pasar de ${Math.min(sale, entra)}.`; }
  else { $("mLim").textContent = "—"; $("dLim").textContent = "Agrega aristas para ver el límite."; }
}
function explicacion() {
  const g = G(), p = pasoActual(), f = p.fase; let chip, t;
  if (construyendo()) { chip = `PRÁCTICA · ITERACIÓN ${g.caminos.length + 1}`; t = textoConstruccion(); }
  else if (f === "sin ejecutar") {
    chip = "SIN EJECUTAR";
    t = "1. Elige el número de nodos arriba y pulsa Manual (aparecen sin aristas) o Aleatorio.\n\n"
      + "2. Activa «Conectar con clic»: toca un vértice y luego otro, y escribe la capacidad.\n\n"
      + "3. Elige una o varias fuentes y sumideros (botones verde y rojo). Con varios se crean S y T.\n\n"
      + "4. Pulsa Calcular flujo y recorre las iteraciones con Siguiente.\n\n"
      + "Modo Práctica: tú armas cada camino, calculas Δ y decides cuándo devolver flujo.";
  } else if (f === "inicial") {
    chip = "ESTADO INICIAL";
    t = `Paso 1. f(e) = 0 para toda arista: cada arco queda como (capacidad, 0).\n\nPaso 2. La fuente ${nom(g.fuente)} se etiqueta con (−, ∞).\n\n`
      + (g.evitar ? "Ford-Fulkerson (sin flujo negativo) repite:\n  1. Buscar un camino con arcos directos libres (c − f > 0), en orden (DFS), revisando que después todavía se pueda llegar al máximo sin devolver flujo.\n  2. Calcular su cuello de botella Δ y sumarlo.\n"
        : "Ford-Fulkerson repite:\n  1. Tomar el primer camino fuente → sumidero con arcos directos libres (c − f > 0), en orden (DFS).\n  2. Calcular su cuello de botella Δ y sumarlo.\n  Si una arista se llena y ya no hay camino directo, pero todavía se puede mandar más flujo, se aplica flujo negativo UNA sola vez: se devuelve flujo por una arista para redirigirlo.\n")
      + `Termina cuando no hay más caminos.\n\nIteraciones necesarias: ${g.caminos.length}  (con flujo negativo: ${g.caminos.filter(c => c.negativo).length})\n\nPulsa Siguiente para ver el primer camino aumentante.`;
  } else if (f === "camino") {
    chip = `ITERACIÓN ${p.it} · A`;
    const L = ["PASO A · CAMINO DE AUMENTO", textoCamino(p.camino), ""];
    if (p.descartado) { L.push("Camino descartado: " + textoCamino(p.descartado.ruta.map(([u, v]) => [u, v, 1])) + `  (+${p.descartado.aumento})`,
      p.descartado.motivo === "varios" ? "Con ese camino, más adelante habría que aplicar flujo negativo más de una vez. Se toma el siguiente en orden."
        : "Si se mandara ese flujo, alguna arista quedaría llena y luego habría que devolver flujo. Como sí existe otra forma, se elige este camino.", ""); }
    L.push("Etiquetas de los vértices (anterior, Δ):");
    for (const [x, [a, d]] of g.etiquetasCamino(p.camino, p.residuales)) L.push(`  ${nom(x)}(${a}, ${d === null ? INF : d})`);
    L.push("", "Capacidad residual de cada arco del camino:");
    const disp = []; let inv = false;
    p.camino.forEach(([u, v, t], i) => { const r = p.residuales[i];
      if (t === 1 && g.esF(u, v)) { L.push(`  (${nom(u)}, ${nom(v)})  ${INF} (arista ficticia)`); disp.push(INF); }
      else if (t === 1) { L.push(`  (${nom(u)}, ${nom(v)})  c − f = ${g.cap.get(K(u, v))} − ${p.flujo.get(K(u, v))} = ${r}`); disp.push(r); }
      else { inv = true; const fo = p.flujo.get(K(v, u)); L.push(`  (${nom(u)}, ${nom(v)})  ARCO INVERSO: f(${nom(u)}, ${nom(v)}) = −f(${nom(v)}, ${nom(u)}) = −${fo}`, `      c_f = 0 − (−${fo}) = ${r}  (flujo que se puede devolver)`); disp.push(r); } });
    L.push("", `Δ = mín{${disp.join(", ")}} = ${p.aumento}`, "", `Flujo total actual: ${p.total}`, "");
    if (inv) { const dev = p.camino.filter(x => x[2] === -1).map(([u, v]) => `${nom(v)} → ${nom(u)}`).join(", ");
      L.push(`¿POR QUÉ FLUJO NEGATIVO AQUÍ? Se llegó a |f| = ${p.total} y ya no queda ningún camino con arcos directos libres, pero el máximo es ${g.flujoMax}: una arista se llenó y aún se puede seguir mandando. Se aplica flujo negativo UNA sola vez, devolviendo flujo por ${dev}.`, "",
        `FLUJO NEGATIVO: el camino recorre una arista en sentido contrario. En el paso B su flujo DISMINUIRÁ en Δ = ${p.aumento}; ese flujo se redirige por otra ruta hacia el sumidero.`, ""); }
    L.push("En el grafo, el camino va en naranja y cada vértice muestra su etiqueta. Pulsa Siguiente para actualizar los flujos.");
    t = L.join("\n");
  } else if (f === "aumento") {
    chip = `ITERACIÓN ${p.it} · B`;
    const L = ["PASO B · ACTUALIZAR LOS FLUJOS", textoCamino(p.camino), `Arcos directos: f + Δ.  Arcos inversos: f − Δ  (Δ = ${p.aumento}).`, "", "Aristas modificadas (c, f):"];
    for (const [u, v, a, d] of p.cambios) { const c = g.textoCap(u, v);
      L.push(`  (${nom(u)}, ${nom(v)}):  (${c}, ${a}) → (${c}, ${d})` + (d < a ? `  ← flujo negativo: se devuelven ${a - d}` : d === g.cap.get(K(u, v)) ? "  llena" : "")); }
    L.push("", `|f| = ${p.total - p.aumento} + ${p.aumento} = ${p.total}`); t = L.join("\n");
  } else { chip = "TERMINADO"; t = "No quedan caminos aumentantes en la red residual.\n\n" + textoResultado(); }
  $("chip").textContent = chip; $("texto").textContent = t;
}
function textoResultado() {
  const g = G(), c = g.corte; if (!c) return "Aún no se ejecutó el algoritmo.";
  const L = ["SOLUCIÓN COMPLETA", "", textoTerminales(), `FLUJO MÁXIMO  |f| = ${g.flujoMax}`];
  if (g.S !== null) { L.push("  Aporte de cada fuente:"); for (const x of g.fuentes) L.push(`    ${letra(x)} envía ${g.flujo.get(K(g.S, x))}`); }
  if (g.T !== null) { L.push("  Llega a cada sumidero:"); for (const x of g.sumideros) L.push(`    ${letra(x)} recibe ${g.flujo.get(K(x, g.T))}`); }
  L.push("", "CAMINOS AUMENTANTES UTILIZADOS");
  if (!g.caminos.length) L.push("  Ninguno: no existe camino dirigido de la fuente al sumidero.");
  for (const x of g.caminos) L.push(`  ${String(x.it).padStart(2)}. ${textoCamino(x.camino)}   +${x.aumento}   (acumulado ${x.total})` + (x.negativo ? "   ← flujo negativo" : ""));
  L.push("", "ASIGNACIÓN DE FLUJO POR ARISTA", "  arista       (c, f)        uso");
  for (const [u, v, cap] of g.aristas()) { const f = g.flujo.get(K(u, v));
    const uso = g.esF(u, v) ? "ficticia" : f === cap ? "llena" : f === 0 ? "sin uso" : Math.round(100 * f / cap) + " %";
    L.push(`  (${nom(u)}, ${nom(v)})     ${`(${g.textoCap(u, v)}, ${f})`.padEnd(12)}  ${uso}`); }
  L.push("", "CORTE MÍNIMO (S, T)", `  S = { ${c.S.map(nom).join(", ")} }`, `  T = { ${c.T.map(nom).join(", ")} }`, "  Arcos que van de S a T:");
  for (const [u, v] of c.ida) L.push(`    (${nom(u)}, ${nom(v)})   capacidad ${g.textoCap(u, v)}`);
  L.push(`  c(S, T) = ${c.ida.map(([u, v]) => g.textoCap(u, v)).join(" + ") || "0"} = ${c.capacidad}`);
  L.push("", "VERIFICACIÓN", `  |f| = ${g.flujoMax} = c(S, T) = ${c.capacidad}  ${g.flujoMax === c.capacidad ? "✓" : "✗"}`,
    "  Ningún flujo supera su capacidad  ✓", "", "Por el Teorema del Flujo Máximo y Corte Mínimo, como |f| = c(S, T), el flujo encontrado es máximo.");
  if (g.caminos.some(x => x.negativo)) {
    const cp = g.copia(); cp.ejecutar(true);
    L.push("", "¿SE PODÍA EVITAR EL FLUJO NEGATIVO?", `  Sí: eligiendo estos caminos se llega al mismo flujo máximo (${cp.flujoMax}) sin devolver flujo:`);
    for (const x of cp.caminos) L.push(`  ${String(x.it).padStart(2)}. ${[cp.nombre(x.camino[0][0]), ...x.camino.map(p => cp.nombre(p[1]))].join(" → ")}   +${x.aumento}`);
  }
  return L.join("\n");
}
function evolucion() {
  const g = G(), svg = $("evol"), W = svg.clientWidth || 320, H = 130, cam = g.caminos, p = pasoActual();
  svg.setAttribute("viewBox", `0 0 ${W} ${H}`);
  if (!cam.length) { svg.innerHTML = `<text x="${W / 2}" y="${H / 2}" text-anchor="middle" fill="var(--muted)" style="font-size:12px">Calcula el flujo para ver cómo crece en cada iteración.</text>`; return; }
  const apl = p.fase === "final" ? cam.length : p.fase === "aumento" ? p.it : p.fase === "camino" ? p.it - 1 : construyendo() ? cam.length : 0;
  const max = Math.max(1, cam[cam.length - 1].total, g.objetivo || 0), iz = 32, de = 10, ar = 18, ab = 22, ux = W - iz - de, uy = H - ar - ab;
  const hueco = ux / Math.max(cam.length, 1), b = Math.max(4, Math.min(34, hueco * .65));
  let s = `<line x1="${iz}" y1="${H - ab}" x2="${W - de}" y2="${H - ab}" stroke="var(--line)"/><text x="${iz - 5}" y="${ar + 4}" text-anchor="end" fill="var(--muted)" style="font:600 10px var(--f-mono)">${max}</text><text x="${iz - 5}" y="${H - ab + 3}" text-anchor="end" fill="var(--muted)" style="font:600 10px var(--f-mono)">0</text>`;
  cam.forEach((c, i0) => { const i = i0 + 1, x = iz + hueco * (i - .5), y = ar + uy * (1 - c.total / max), yb = ar + uy * (1 - (c.total - c.aumento) / max);
    const hecho = i <= apl, actual = p.fase === "camino" && i === p.it && !st.practica;
    if (st.practica && !hecho) return;
    const col = hecho ? (i === apl ? "var(--path)" : c.negativo ? "var(--neg)" : "var(--accent)") : actual ? "var(--path)" : "var(--line)";
    s += `<rect x="${x - b / 2}" y="${yb}" width="${b}" height="${H - ab - yb}" fill="${hecho ? "var(--accent-soft)" : "none"}" stroke="var(--line)"${hecho ? "" : ' stroke-dasharray="3 2"'}/>`;
    s += `<rect x="${x - b / 2}" y="${y}" width="${b}" height="${Math.max(0, yb - y)}" fill="${hecho ? col : "none"}" stroke="${col}"${hecho ? "" : ' stroke-dasharray="3 2"'}/>`;
    if (hecho || actual) s += `<text x="${x}" y="${y - 5}" text-anchor="middle" fill="${col}" style="font:700 10px var(--f-mono)">+${c.aumento}</text>`;
    s += `<text x="${x}" y="${H - ab + 14}" text-anchor="middle" fill="var(--muted)" style="font:600 10px var(--f-mono)">${i}</text>`; });
  svg.innerHTML = s;
}

/* =========================================================
   MODO PRÁCTICA
   ========================================================= */
function iniciarPractica() {
  const g = G();
  try { g.preparar(false); } catch (e) { mensaje("No se pudo calcular", e.message); return; }
  st.practica = true; st.respuestas = {}; st.origen = null; st.sel = null; setEditar(false);
  nuevaIteracion(); st.paso = 0; st.vista = "Red residual"; $("vista").value = st.vista;
  feedback(`Arma el camino tocando los vértices desde ${nom(g.fuente)} hasta ${nom(g.sumidero)}.`, "info");
  estado("Modo práctica: tú eliges cada camino aumentante.");
  render();
}
function nuevaIteracion() { st.cam = [G().fuente]; st.listo = false; st.intentos = 0; st.nivelPista = 0; st.pistaArista = null; st.sugerencia = null; $("delta").value = ""; }
function feedback(t, cls) { const e = $("fb"); e.textContent = t; e.className = "fb " + cls; }
function rutaUsuario() { const r = []; for (let i = 0; i + 1 < st.cam.length; i++) { const a = G().arcoLibre(st.cam[i], st.cam[i + 1]); if (a) r.push([st.cam[i], st.cam[i + 1], a[0], a[1]]); } return r; }
function atascado() { const g = G(); return st.practica && !g.terminado() && !g.hayDirecto(); }
function opcionesDesde(x) {
  const g = G(), at = atascado(), r = [];
  for (let y = 0; y < g.n; y++) { if (st.cam.includes(y)) continue; const a = g.arcoLibre(x, y); if (!a || (a[0] === -1 && !at)) continue; r.push([y, a[0], a[1]]); }
  return r;
}
function clicPractica(nodo) {
  const g = G(), cam = st.cam, ult = cam[cam.length - 1];
  if (nodo === ult && cam.length > 1) { cam.pop(); st.listo = false; feedback(`Retrocediste a ${nom(cam[cam.length - 1])}.`, "mute"); render(); return; }
  if (st.listo) { feedback("El camino ya llegó al sumidero: escribe Δ y pulsa Comprobar (o toca el sumidero para retroceder).", "mute"); return; }
  if (nodo === g.fuente) { st.cam = [g.fuente]; feedback("Camino reiniciado desde la fuente.", "mute"); render(); return; }
  if (cam.includes(nodo)) { feedback(`${nom(nodo)} ya está en el camino: un camino no repite vértices.`, "bad"); return; }
  const a = g.arcoLibre(ult, nodo);
  if (!a) { feedback(`No se puede ir de ${nom(ult)} a ${nom(nodo)}: no hay capacidad libre.`, "bad"); return; }
  if (a[0] === -1 && !atascado()) { feedback(`${nom(ult)} → ${nom(nodo)} sería devolver flujo. Todavía existe un camino con aristas libres: el flujo negativo solo se usa cuando ya no queda ninguno.`, "bad"); return; }
  cam.push(nodo); st.sugerencia = null;
  if (nodo === g.sumidero) { st.listo = true; feedback("Camino completo. Calcula Δ (la MENOR capacidad libre del camino), escríbelo y pulsa Comprobar.", "info"); render(); $("delta").focus(); return; }
  feedback("Camino: " + cam.map(nom).join(" → "), "mute"); render();
}
function comprobar() {
  if (!(construyendo() && st.listo)) { feedback("Primero arma el camino hasta el sumidero.", "mute"); return; }
  const g = G(), cam = rutaUsuario(), ruta = cam.map(([u, v, t]) => [u, v, t]), res = cam.map(p => p[3]), ok = Math.min(...res);
  const r = parseInt($("delta").value, 10); if (Number.isNaN(r)) { feedback("Escribe un número entero para Δ.", "bad"); return; }
  const it = g.caminos.length + 1;
  if (r !== ok) {
    st.intentos++; st.respuestas[it] = false;
    const vals = ruta.map(([u, v, t], i) => (t === 1 && g.esF(u, v)) ? INF : res[i]).join(", ");
    feedback(st.intentos === 1 ? `✗ ${r} no es correcto. Δ es la MENOR capacidad libre entre los arcos del camino. Inténtalo otra vez.`
      : st.intentos === 2 ? `✗ ${r} tampoco. Pista: las capacidades libres del camino son ${vals}.` : `✗ Δ = mín{${vals}} = ${ok}. Escríbelo para continuar.`, "bad");
    $("delta").value = ""; controlesPractica(); return;
  }
  if (!(it in st.respuestas)) st.respuestas[it] = st.intentos === 0;
  g.aplicarInteractivo(cam); nuevaIteracion(); irPaso(g.hist.length - 1);
  if (g.terminado()) { feedback(`✓ ¡Llegaste al flujo máximo: ${g.flujoMax}! Lo certifica el corte mínimo (en el grafo).`, "ok"); return; }
  feedback(`✓ Correcto, Δ = ${ok}. Flujo total: ${g._total}. ` + (atascado() ? "Ya no queda camino directo, pero aún se puede mandar más: usa flujo negativo (pide una Pista si lo necesitas)." : "Elige el siguiente camino."), "ok");
}
function pista() {
  if (!construyendo()) return;
  const g = G(), at = atascado(); st.nivelPista = Math.min(3, st.nivelPista + 1);
  const [sug] = g.siguienteAutomatico(), ruta = sug ? sug.map(([u, v, t]) => [u, v, t]) : []; let t = "";
  if (st.nivelPista === 1) t = at ? "Ya no hay camino directo: alguna arista se llenó. Busca una arista llena cuyo flujo puedas redirigir (flujo negativo)."
    : `Busca un camino de ${nom(g.fuente)} a ${nom(g.sumidero)} usando solo aristas con capacidad libre (c − f > 0).`;
  else if (st.nivelPista === 2) {
    if (at) { const inv = ruta.filter(p => p[2] === -1).map(([u, v]) => [v, u]);
      if (inv.length) { st.pistaArista = inv[0]; t = `Conviene devolver flujo por ${nom(inv[0][0])} → ${nom(inv[0][1])} (marcada en magenta): llega a ${nom(inv[0][1])} y toca ${nom(inv[0][0])}.`; } }
    else { const op = opcionesDesde(st.cam[st.cam.length - 1]); t = `Desde ${nom(st.cam[st.cam.length - 1])} puedes avanzar a: ${op.map(o => nom(o[0])).join(", ") || "ninguno"}. Si ninguno lleva al sumidero, retrocede.`; }
  } else { st.sugerencia = ruta; t = "Camino sugerido (punteado en el grafo): " + textoCamino(ruta); }
  feedback(`Pista ${st.nivelPista}: ${t}`, "hint"); render();
}
function sugerir() {
  if (!construyendo()) return; const [s] = G().siguienteAutomatico(); if (!s) return;
  st.sugerencia = s.map(([u, v, t]) => [u, v, t]);
  feedback("Sugerencia (punteada en el grafo): " + textoCamino(st.sugerencia) + ". Ármala tocando los vértices o pulsa «Usar sugerencia».", "hint"); render();
}
function usarSugerencia() {
  if (!(construyendo() && st.sugerencia)) return;
  st.cam = [st.sugerencia[0][0], ...st.sugerencia.map(p => p[1])]; st.sugerencia = null; st.listo = true;
  feedback("Camino listo. Calcula Δ y pulsa Comprobar.", "info"); render(); $("delta").focus();
}
function deshacerCamino() {
  const g = G(); if (!st.practica || !g.deshacerUltimo()) { feedback("No hay caminos para deshacer.", "mute"); return; }
  delete st.respuestas[g.caminos.length + 1]; nuevaIteracion(); irPaso(g.hist.length - 1);
  feedback(`Último camino deshecho. Flujo total: ${g._total}. Elige otro.`, "mute");
}
function controlesPractica() {
  $("practica").hidden = !st.practica; if (!st.practica) return;
  const c = construyendo(), g = G();
  $("bComprobar").disabled = !(c && st.listo); $("bPista").disabled = $("bSugerir").disabled = !c;
  $("bUsar").disabled = !(c && st.sugerencia); $("bDeshacerCamino").disabled = !g.caminos.length;
  const r = Object.values(st.respuestas);
  $("score").textContent = `Caminos: ${g.caminos.length} · Δ al primer intento: ${r.filter(Boolean).length}/${r.length}`;
}
function textoConstruccion() {
  const g = G(), cam = st.cam, ult = cam[cam.length - 1];
  const L = [`MODO PRÁCTICA · ITERACIÓN ${g.caminos.length + 1}`, `Flujo actual: |f| = ${g._total}`, "", "Camino: " + cam.map(nom).join(" → "), ""];
  if (st.listo) L.push("Busca la capacidad libre de cada arco en la red residual y escribe Δ abajo.");
  else { L.push(`Desde ${nom(ult)} puedes ir a:`); const op = opcionesDesde(ult);
    for (const [y, t] of op) L.push(t === 1 ? `  ${nom(y)}  (anillo verde)` : `  ${nom(y)}⁻  (devolver flujo: flecha magenta)`);
    if (!op.length) L.push(cam.length > 1 ? `  ninguno: toca ${nom(ult)} para retroceder` : "  ninguno"); }
  if (atascado()) L.push("", "Ya no queda camino directo, pero aún se puede mandar más flujo: puedes devolver flujo por la arista que elijas.");
  L.push("", "Toca el último vértice para retroceder.");
  return L.join("\n");
}

/* =========================================================
   VENTANAS (dentro de la página)
   ========================================================= */
function modal(titulo, html, botones = [], { cancelar = "Cancelar" } = {}) {
  const v = document.createElement("div"); v.className = "velo";
  v.innerHTML = `<div class="modal" role="dialog" aria-modal="true" aria-label="${esc(titulo)}"><h3>${esc(titulo)}</h3><div class="cuerpo">${html}</div><div class="pie"></div></div>`;
  const pie = v.querySelector(".pie"), cerrar = () => v.remove();
  if (cancelar) { const b = document.createElement("button"); b.className = "btn"; b.textContent = cancelar; b.onclick = cerrar; pie.appendChild(b); }
  for (const [t, fn, cls] of botones) { const b = document.createElement("button"); b.className = "btn " + (cls || ""); b.textContent = t;
    b.onclick = () => { if (fn() !== false) cerrar(); }; pie.appendChild(b); }
  v.addEventListener("click", e => { if (e.target === v) cerrar(); });
  v.addEventListener("keydown", e => { if (e.key === "Escape") cerrar(); });
  document.body.appendChild(v);
  const foco = v.querySelector("input") || pie.lastChild; foco && foco.focus();
  return v;
}
function mensaje(t, m) { modal(t, `<p style="color:var(--ink)">${esc(m)}</p>`, [], { cancelar: "Aceptar" }); }
function pedirNumero(titulo, texto, valor, extra, ok) {
  const v = modal(titulo, `<p>${esc(texto)}</p><input id="pn" type="number" min="1" value="${valor}" inputmode="numeric">`,
    [...extra.map(([t, fn]) => [t, fn, "danger"]), ["Guardar", () => { const c = parseInt($("pn").value, 10); if (!(c > 0)) { $("pn").focus(); return false; } ok(c); }, "primary"]]);
  $("pn").select(); $("pn").addEventListener("keydown", e => { if (e.key === "Enter") v.querySelector(".pie .primary").click(); });
}
function dlgTerminales() {
  aPrincipal(); const g = G(); let filas = "";
  for (let x = 0; x < g.n0; x++) { const e = g.entradasOrig(x).length, s = g.salidasOrig(x).length;
    filas += `<tr><td><b>${letra(x)}</b></td><td><input type="checkbox" id="tf${x}" ${g.fuentes.includes(x) ? "checked" : ""}></td><td><input type="checkbox" id="ts${x}" ${g.sumideros.includes(x) ? "checked" : ""}></td><td style="color:var(--muted)">${e} entran · ${s} salen${!e && s ? " (sugerida fuente)" : s === 0 && e ? " (sugerido sumidero)" : ""}</td></tr>`; }
  const v = modal("Fuentes y sumideros", `<p>Marca una o varias fuentes y uno o varios sumideros. Con 2 o más fuentes se crea la superfuente S, y con 2 o más sumideros el supersumidero T, unidos con aristas ∞.</p>
    <div class="wrapx"><table class="tabla"><tr><th>Vértice</th><th>Fuente</th><th>Sumidero</th><th>Aristas</th></tr>${filas}</table></div>`,
    [["Sugerir automáticamente", () => { const f = g.fuentesPosibles(), s = g.sumiderosPosibles(); for (let x = 0; x < g.n0; x++) { $("tf" + x).checked = f.includes(x); $("ts" + x).checked = s.includes(x); } return false; }],
     ["Aplicar", () => { const f = [], s = []; for (let x = 0; x < g.n0; x++) { if ($("tf" + x).checked) f.push(x); if ($("ts" + x).checked) s.push(x); }
        try { guardarUndo(); g.definirTerminales(f, s); } catch (e) { st.undo.pop(); mensaje("Revisa la selección", e.message); return false; }
        redCambiada("Fuentes y sumideros actualizados. Pulsa Calcular flujo."); }, "primary"]]);
  for (let x = 0; x < g.n0; x++) { $("tf" + x).onchange = () => { if ($("tf" + x).checked) $("ts" + x).checked = false; }; $("ts" + x).onchange = () => { if ($("ts" + x).checked) $("tf" + x).checked = false; }; }
  return v;
}
function dlgMatriz() {
  aPrincipal(); const g = G(), n = g.n0;
  let h = `<p>Fila = origen, columna = destino. Escribe la capacidad o deja vacío si no hay arista.</p><div class="wrapx"><table class="mtx"><tr><th>de\\a</th>`;
  for (let j = 0; j < n; j++) h += `<th>${letra(j)}</th>`; h += "</tr>";
  for (let i = 0; i < n; i++) { h += `<tr><th>${letra(i)}</th>`;
    for (let j = 0; j < n; j++) h += i === j ? `<td style="text-align:center;color:var(--muted)">—</td>` : `<td><input type="text" inputmode="numeric" id="m${i}_${j}" value="${g.cap.get(K(i, j)) || ""}"></td>`;
    h += "</tr>"; }
  h += `</table></div><p id="mEstado" style="font-weight:700"></p>`;
  const leer = () => { const a = [], err = [];
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { if (i === j) continue; const el = $(`m${i}_${j}`), t = el.value.trim(); el.className = "";
      if (!t) continue; if (!/^\d+$/.test(t) || +t <= 0) { el.className = "badc"; err.push(`(${letra(i)}, ${letra(j)}) debe ser entero positivo`); continue; }
      el.className = "okc"; a.push([i, j, +t]); }
    $("mEstado").textContent = err.length ? "✗ " + err.slice(0, 3).join("; ") : `✓ ${a.length} aristas.`; $("mEstado").style.color = err.length ? "var(--sink)" : "var(--src)";
    return [a, err]; };
  modal("Matriz de capacidades", h, [["Aplicar", () => { const [a, err] = leer(); if (err.length) return false;
    const nuevo = new Grafo(n);
    try { a.sort((x, y) => x[0] - y[0] || x[1] - y[1]).forEach(([i, j, c]) => nuevo.agregar(i, j, c)); } catch (e) { $("mEstado").textContent = "✗ " + e.message; $("mEstado").style.color = "var(--sink)"; return false; }
    try { nuevo.definirTerminales(g.fuentes, g.sumideros); } catch (e) { try { nuevo.definirTerminales(nuevo.fuentesPosibles().length ? nuevo.fuentesPosibles() : [0], nuevo.sumiderosPosibles().length ? nuevo.sumiderosPosibles() : [n - 1]); } catch (e2) {} }
    const antes = capturar(); asignar(nuevo, "Red ingresada por matriz", "Red cargada desde la matriz. Pulsa Calcular flujo."); st.undo.push(antes); render(); }, "primary"]]);
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j) $(`m${i}_${j}`).addEventListener("input", leer);
  leer();
}
function persistir() { try { localStorage.setItem("flujo-grafos", JSON.stringify(st.guardados)); } catch (e) {} }
function dlgGuardados() {
  aPrincipal(); let elegido = null;
  const pintar = () => { const filas = st.guardados.map((x, i) => `<tr data-i="${i}" class="${i === elegido ? "sel" : ""}" style="cursor:pointer"><td><b>${esc(x.nombre)}</b></td><td>${x.n}</td><td>${x.aristas.length}</td><td>${x.f.map(letra).join(", ")}</td><td>${x.s.map(letra).join(", ")}</td><td>${esc(x.hora)}</td></tr>`).join("");
    $("gl").innerHTML = st.guardados.length ? `<table class="tabla"><tr><th>Nombre</th><th>Nodos</th><th>Aristas</th><th>Fuentes</th><th>Sumideros</th><th>Guardado</th></tr>${filas}</table>` : `<p>Aún no hay grafos guardados. Escribe un nombre y pulsa «Guardar el actual».</p>`;
    $("gl").querySelectorAll("tr[data-i]").forEach(tr => tr.onclick = () => { elegido = +tr.dataset.i; pintar(); }); };
  const v = modal("Grafos guardados", `<p>Se guardan en este navegador. Toca una fila para elegirla.</p>
     <div style="display:flex;gap:6px;flex-wrap:wrap;margin-bottom:10px"><input type="text" id="gNombre" placeholder="Nombre del grafo" value="${esc(st.nombre || "Grafo " + (st.guardados.length + 1))}"><button class="btn" id="gGuardar">Guardar el actual</button></div>
     <div class="wrapx" id="gl"></div>`,
    [["Eliminar", () => { if (elegido === null) return false; st.guardados.splice(elegido, 1); elegido = null; persistir(); pintar(); return false; }, "danger"],
     ["Abrir", () => { if (elegido === null) return false; const x = st.guardados[elegido]; const g = reconstruir(x); asignar(g, x.nombre, `Grafo «${x.nombre}» cargado. Pulsa Calcular flujo.`); if (x.layout) st.layout = JSON.parse(JSON.stringify(x.layout)); render(); }, "primary"]], { cancelar: "Cerrar" });
  $("gGuardar").onclick = () => { const nombre = $("gNombre").value.trim(); if (!nombre) return; if (!G().originales().length) { $("gl").insertAdjacentHTML("afterbegin", "<p style='color:var(--sink)'>Agrega aristas antes de guardar.</p>"); return; }
    const foto = { nombre, ...capturar(), layout: st.layout, hora: new Date().toLocaleTimeString() };
    const i = st.guardados.findIndex(x => x.nombre === nombre); if (i >= 0) st.guardados[i] = foto; else st.guardados.push(foto);
    st.nombre = nombre; persistir(); pintar(); estado(`Grafo «${nombre}» guardado.`); };
  pintar(); return v;
}
function dlgCortes() {
  const g = G(); if (!g.corte) { mensaje("Primero calcula el flujo", "Pulsa Calcular flujo para comparar todos los cortes."); return; }
  const fs = new Set([g.tf, ...g.fuentes]), ft = new Set([g.ts, ...g.sumideros]), lib = [];
  for (let x = 0; x < g.n; x++) if (!fs.has(x) && !ft.has(x)) lib.push(x);
  if (lib.length > 12) { mensaje("Demasiados cortes", `Hay ${2 ** lib.length} cortes posibles; la tabla se muestra con 12 vértices libres como máximo.`); return; }
  const filas = [];
  for (let m = 0; m < 2 ** lib.length; m++) { const S = new Set(fs); lib.forEach((x, i) => { if (m >> i & 1) S.add(x); }); filas.push(g.describirCorte(S)); }
  filas.sort((a, b) => a.capacidad - b.capacidad || a.S.length - b.S.length);
  const L = ["Fuente en S, sumidero en T; los demás vértices se reparten de todas las formas posibles:", `2^${lib.length} = ${2 ** lib.length} cortes.`, "", `${"S".padEnd(34)} ${"c(S,T)".padStart(7)} ${"f(S,T)".padStart(7)}`, "-".repeat(52)];
  for (const c of filas) L.push(`{${c.S.map(nom).join(", ")}}`.padEnd(34) + ` ${String(c.infinito ? INF : c.capacidad).padStart(7)} ${String(c.neto).padStart(7)}` + (c.minimo ? "  ★ mínimo" : ""));
  L.push("", `|f| = ${g.flujoMax}. Todos los cortes cumplen f(S, T) = |f| ≤ c(S, T).`, `Cortes mínimos: ${filas.filter(c => c.minimo).length} (capacidad ${g.corte.capacidad}).`, "Teorema: máx |f| = mín c(S, T).");
  textoModal("Tabla de todos los cortes", L.join("\n"));
}
function textoModal(t, texto) {
  modal(t, `<pre class="mono" id="tm">${esc(texto)}</pre>`, [["Copiar texto", () => {
    const ok = () => estado("Texto copiado.");
    try { navigator.clipboard.writeText(texto).then(ok, () => { getSelection().selectAllChildren($("tm")); estado("Selecciona y copia el texto manualmente."); }); } catch (e) { getSelection().selectAllChildren($("tm")); }
    return false; }]], { cancelar: "Cerrar" });
}

/* =========================================================
   EVENTOS
   ========================================================= */
function aSvg(ev) { const svg = $("lienzo"), p = svg.createSVGPoint(); p.x = ev.clientX; p.y = ev.clientY; return p.matrixTransform(svg.getScreenCTM().inverse()); }
function clicNodo(x) {
  const g = G();
  if (st.mover) { const m = st.mover; st.mover = null; aPrincipal();
    if (x >= G().n0) { estado("Cambio cancelado."); render(); return; }
    const [u, v] = m.e; m.tipo === "origen" ? moverArista(u, v, x, v) : moverArista(u, v, u, x); return; }
  if (construyendo()) { clicPractica(x); return; }
  if (!st.editar) return;
  aPrincipal();
  if (x >= g.n0) { estado("Las aristas de S y T son automáticas (∞). Elige vértices originales."); return; }
  if (st.origen === null) { st.origen = x; st.sel = null;
    estado(`Origen ${nom(x)}. Ahora toca el destino (sin ciclos: ${G().destinosValidos(x).map(nom).join(", ") || "ninguno"}).`); render(); return; }
  const u = st.origen; st.origen = null; if (u === x) { render(); return; }
  render(); conectar(u, x);
}
function clicArista(u, v, ret) {
  if (construyendo()) { if (ret) { if (st.cam[st.cam.length - 1] === v) clicPractica(u); else feedback(`Para devolver flujo por ${nom(u)} → ${nom(v)}, primero llega a ${nom(v)}.`, "mute"); } return; }
  if (!st.editar) return;
  aPrincipal(); hojaArista(u, v);
}
function enlazar() {
  const svg = $("lienzo");
  svg.addEventListener("pointerdown", ev => {
    const n = ev.target.closest("[data-node]");
    if (n) { st.drag = { nodo: +n.dataset.node, x0: ev.clientX, y0: ev.clientY, movido: false, id: ev.pointerId }; }
  });
  window.addEventListener("pointermove", ev => {
    const d = st.drag; if (!d || d.id !== ev.pointerId) return;
    if (!d.movido && Math.hypot(ev.clientX - d.x0, ev.clientY - d.y0) < 6) return;
    d.movido = true; const p = aSvg(ev); if (!st.layout) st.layout = layoutAuto();
    st.layout[nom(d.nodo)] = { x: Math.max(40, p.x), y: Math.max(40, p.y) }; dibujar();
  });
  window.addEventListener("pointerup", ev => {
    const d = st.drag; st.drag = null;
    if (d && d.id === ev.pointerId) { if (d.movido) estado(`Vértice ${nom(d.nodo)} movido.`); else clicNodo(d.nodo); return; }
  });
  svg.addEventListener("click", ev => {
    if (ev.target.closest("[data-node]")) return;
    const e = ev.target.closest("[data-edge],[data-ret]");
    if (e) { const [u, v] = (e.dataset.edge || e.dataset.ret).split(",").map(Number); clicArista(u, v, !!e.dataset.ret); return; }
    if (st.origen !== null || st.sel || st.mover) { st.origen = null; st.sel = null; st.mover = null; estado("Selección cancelada."); render(); }
  });
  $("bManual").onclick = () => nuevoManual(+$("n").value);
  $("n").addEventListener("change", () => { const n = Math.min(16, Math.max(7, +$("n").value || 7)); if (n !== G().n0) nuevoManual(n); else $("n").value = n; });
  $("bAleatorio").onclick = () => { aPrincipal(); const n = Math.min(16, Math.max(7, +$("n").value || 7)); const antes = capturar(); asignar(aleatorio(n), "Grafo aleatorio"); st.undo.push(antes); render(); };
  $("bFuentes").onclick = $("bSumideros").onclick = dlgTerminales;
  $("bCalcular").onclick = calcular; $("bLimpiar").onclick = limpiar;
  $("modo").onchange = () => { quitarPestanas(); if ($("modo").value === "practica") { if (G().originales().length) iniciarPractica(); else { estado("Modo práctica: crea el grafo y pulsa Calcular flujo."); render(); } }
    else { st.practica = false; if (G().hist.length) calcular(); else render(); estado("Modo automático: el programa resuelve paso a paso."); } };
  $("vista").onchange = () => { st.vista = $("vista").value; if (st.vista === "Corte mínimo" && !G().corte) { st.vista = "Red original"; $("vista").value = st.vista; estado("Pulsa Calcular flujo para obtener el corte mínimo."); }
    else if (st.vista === "Corte mínimo") st.paso = G().hist.length - 1; render(); };
  $("tabCon").onclick = () => cambiarPestana("principal"); $("tabSin").onclick = () => cambiarPestana("alternativa");
  $("bAlejar").onclick = () => { st.zoom = Math.max(.5, +(st.zoom - .15).toFixed(2)); dibujar(); };
  $("bAcercar").onclick = () => { st.zoom = Math.min(2.5, +(st.zoom + .15).toFixed(2)); dibujar(); };
  const fac = (k, d) => { const ant = st[k]; st[k] = Math.min(3, Math.max(.75, +(st[k] + d).toFixed(2)));
    k === "fa" ? escalar(st.fa / ant, 1) : escalar(1, st.fh / ant); estado(`${k === "fa" ? "Ancho" : "Alto"} del grafo: ${Math.round(st[k] * 100)} %`); dibujar(); };
  $("bAnchoM").onclick = () => fac("fa", -.25); $("bAnchoP").onclick = () => fac("fa", .25);
  $("bAltoM").onclick = () => fac("fh", -.25); $("bAltoP").onclick = () => fac("fh", .25);
  $("bDeshacer").onclick = deshacer;
  $("editar").onchange = () => { aPrincipal(); setEditar($("editar").checked); estado(st.editar ? "Conectar: toca el vértice de origen y luego el de destino. Toca una arista para cambiarla o eliminarla." : "Edición desactivada."); render(); };
  $("autoOrden").onchange = () => { if ($("autoOrden").checked) { reordenar(); render(); estado("Después de cada arista el grafo se acomoda por columnas con el menor número de cruces."); } else estado("Los nodos se quedan donde están; puedes arrastrarlos."); };
  $("bInicio").onclick = () => irPaso(0); $("bAnterior").onclick = () => irPaso(st.paso - 1);
  $("bSiguiente").onclick = () => irPaso(st.paso + 1); $("bResultado").onclick = () => irPaso(G().hist.length - 1);
  $("bComprobar").onclick = comprobar; $("delta").addEventListener("keydown", e => { if (e.key === "Enter") comprobar(); });
  $("bPista").onclick = pista; $("bSugerir").onclick = sugerir; $("bUsar").onclick = usarSugerencia; $("bDeshacerCamino").onclick = deshacerCamino;
  $("bEj7").onclick = () => { aPrincipal(); asignar(ejemplo7(), "Ejemplo de 7 nodos"); render(); };
  $("bEjMulti").onclick = () => { aPrincipal(); asignar(ejemploMulti(), "Ejemplo multifuente", "Fuentes a y b → superfuente S. Sumideros g y h → supersumidero T. Pulsa Calcular flujo."); render(); };
  $("bMatriz").onclick = dlgMatriz; $("bGuardados").onclick = dlgGuardados; $("bCortes").onclick = dlgCortes;
  $("bReporte").onclick = () => { if (!G().corte) { mensaje("Primero calcula el flujo", "Pulsa Calcular flujo para obtener la solución completa."); return; } textoModal("Reporte de la solución", textoResultado()); };
  document.addEventListener("keydown", e => {
    if (document.querySelector(".velo") || /INPUT|SELECT|TEXTAREA/.test(document.activeElement.tagName)) return;
    if (e.key === "ArrowRight") irPaso(st.paso + 1); else if (e.key === "ArrowLeft") irPaso(st.paso - 1);
    else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === "z") { e.preventDefault(); deshacer(); }
    else if ((e.key === "Delete" || e.key === "Backspace") && st.sel) eliminarArista(...st.sel);
    else if (e.key === "Escape") { st.origen = null; st.sel = null; st.mover = null; render(); }
  });
  let rz; window.addEventListener("resize", () => { clearTimeout(rz); rz = setTimeout(() => { dibujar(); evolucion(); }, 80); });
}

/* ---- inicio ---- */
enlazar();
asignar(ejemplo7(), "Ejemplo de 7 nodos", "Ejemplo de 7 nodos cargado. Pulsa Calcular flujo para ver el algoritmo paso a paso.");
render();
window.FlujoApp = { Grafo, st, ejemplo7, ejemploMulti, calcular, irPaso, clicNodo, comprobar, pista, sugerir, usarSugerencia, deshacerCamino, render, construyendo };
