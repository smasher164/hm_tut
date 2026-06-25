(function () {
  const root = document.querySelector('[data-widget="let-generalization-scope"]');
  if (!root) return;

  const textarea = root.querySelector('.lg-textarea');
  const submitBtn = root.querySelector('.lg-submit');
  const backBtn = root.querySelector('.lg-back');
  const stepBtn = root.querySelector('.lg-step');
  const resetBtn = root.querySelector('.lg-reset');
  const naiveRadio = root.querySelector('.lg-mode-naive');
  const scopedRadio = root.querySelector('.lg-mode-scoped');
  const errorEl = root.querySelector('.lg-error');
  const traceEl = root.querySelector('.lg-trace');

  const KEYWORDS = ['fun', 'let', 'in', 'true', 'false'];

  function tokenize(src) {
    const tokens = [];
    let i = 0;
    while (i < src.length) {
      const c = src[i];
      if (/\s/.test(c)) { i++; continue; }
      if (c === '(' || c === ')' || c === '=') { tokens.push({ type: c }); i++; continue; }
      if (c === '-' && src[i + 1] === '>') { tokens.push({ type: '->' }); i += 2; continue; }
      if (/[a-zA-Z_]/.test(c)) {
        let j = i;
        while (j < src.length && /[a-zA-Z0-9_]/.test(src[j])) j++;
        const word = src.slice(i, j);
        if (KEYWORDS.includes(word)) tokens.push({ type: word });
        else tokens.push({ type: 'IDENT', name: word });
        i = j;
        continue;
      }
      throw new Error("unexpected character '" + c + "' at column " + (i + 1));
    }
    return tokens;
  }

  function parse(src) {
    const tokens = tokenize(src);
    let pos = 0;
    function peek() { return tokens[pos]; }
    function consume(type) {
      if (!peek() || peek().type !== type) {
        const got = peek() ? peek().type : 'end of input';
        throw new Error("expected '" + type + "', got '" + got + "'");
      }
      return tokens[pos++];
    }
    function canStartAtom() {
      const t = peek();
      return !!t && (t.type === 'true' || t.type === 'false' || t.type === 'IDENT' || t.type === '(');
    }
    function parseExpr() {
      const t = peek();
      if (!t) throw new Error("expected expression");
      if (t.type === 'fun') {
        pos++;
        const param = consume('IDENT');
        consume('->');
        const body = parseExpr();
        return { kind: 'ELam', param: param.name, body };
      }
      if (t.type === 'let') {
        pos++;
        const id = consume('IDENT');
        consume('=');
        const rhs = parseExpr();
        consume('in');
        const body = parseExpr();
        return { kind: 'ELet', id: id.name, rhs, body };
      }
      return parseApp();
    }
    function parseApp() {
      let result = parseAtom();
      while (canStartAtom()) {
        const next = parseAtom();
        result = { kind: 'EApp', fn: result, arg: next };
      }
      return result;
    }
    function parseAtom() {
      const t = peek();
      if (!t) throw new Error("expected expression");
      if (t.type === 'true') { pos++; return { kind: 'EBool', value: true }; }
      if (t.type === 'false') { pos++; return { kind: 'EBool', value: false }; }
      if (t.type === 'IDENT') { pos++; return { kind: 'EVar', name: t.name }; }
      if (t.type === '(') {
        pos++;
        const e = parseExpr();
        consume(')');
        return e;
      }
      throw new Error("unexpected token '" + t.type + "'");
    }
    const result = parseExpr();
    if (pos !== tokens.length) throw new Error("extra input after expression");
    return result;
  }

  function needsParens(exp, context) {
    if (context === 'app-fn') return exp.kind === 'ELam' || exp.kind === 'ELet';
    if (context === 'app-arg') return exp.kind !== 'EBool' && exp.kind !== 'EVar';
    return false;
  }

  function formatExp(exp, context) {
    let text;
    if (exp.kind === 'EBool') text = exp.value ? 'true' : 'false';
    else if (exp.kind === 'EVar') text = exp.name;
    else if (exp.kind === 'ELam') text = 'fun ' + exp.param + ' -> ' + formatExp(exp.body, 'body');
    else if (exp.kind === 'ELet') text = 'let ' + exp.id + ' = ' + formatExp(exp.rhs, 'rhs') + ' in ' + formatExp(exp.body, 'body');
    else if (exp.kind === 'EApp') text = formatExp(exp.fn, 'app-fn') + ' ' + formatExp(exp.arg, 'app-arg');
    else text = '?';
    if (context && needsParens(exp, context)) return '(' + text + ')';
    return text;
  }

  function force(ty) {
    while (ty.kind === 'TyVar' && ty.ref.link) ty = ty.ref.link;
    return ty;
  }

  function formatTy(ty) {
    ty = force(ty);
    if (ty.kind === 'TyBool') return 'Bool';
    if (ty.kind === 'TyVar') return ty.ref.id;
    if (ty.kind === 'TyArrow') {
      const fromForced = force(ty.from);
      const fStr = fromForced.kind === 'TyArrow' ? '(' + formatTy(ty.from) + ')' : formatTy(ty.from);
      return fStr + ' -> ' + formatTy(ty.to);
    }
    return '?';
  }

  function formatTyRaw(ty) {
    if (ty.kind === 'TyBool') return 'Bool';
    if (ty.kind === 'TyVar') return ty.ref.id;
    if (ty.kind === 'TyArrow') {
      const fStr = ty.from.kind === 'TyArrow' ? '(' + formatTyRaw(ty.from) + ')' : formatTyRaw(ty.from);
      return fStr + ' -> ' + formatTyRaw(ty.to);
    }
    return '?';
  }

  function formatScheme(scheme) {
    if (scheme.forall.length === 0) return '∀_. ' + formatTyRaw(scheme.type);
    return '∀' + scheme.forall.join(' ') + '. ' + formatTyRaw(scheme.type);
  }

  function runInference(program, mode) {
    const state = { scope: 1, gensym: 0, metavars: [], env: [] };
    const events = [];
    let depth = 0;

    function snapshot() {
      return {
        scope: state.scope,
        metavars: state.metavars.map(r => ({
          id: r.id,
          scope: r.scope,
          link: r.link ? formatTy(r.link) : null,
        })),
        env: state.env.map(e => ({ name: e.name, scheme: formatScheme(e.scheme) })),
      };
    }

    function emit(text, tag, kind) {
      events.push({
        depth,
        text,
        tag: tag || '',
        kind: kind || 'neutral',
        state: snapshot(),
      });
    }

    function emitSub(text, kind) {
      events.push({
        depth: depth + 1,
        text,
        tag: '',
        kind: kind || 'neutral',
        state: snapshot(),
      });
    }

    function freshUnboundVar() {
      const id = '?' + state.gensym;
      state.gensym++;
      const ref = { id, scope: state.scope, link: null };
      state.metavars.push(ref);
      return { kind: 'TyVar', ref };
    }

    function occurs(srcRef, ty) {
      ty = force(ty);
      if (ty.kind === 'TyVar') {
        const tgt = ty.ref;
        if (tgt === srcRef) throw new Error('occurs check: ' + srcRef.id + ' would occur in itself');
        const oldScope = tgt.scope;
        const newScope = Math.min(srcRef.scope, tgt.scope);
        if (newScope < oldScope) {
          tgt.scope = newScope;
          if (mode === 'scoped') emitSub(tgt.id + '.scope = min(' + srcRef.scope + '<sub>' + srcRef.id + '</sub>, ' + oldScope + '<sub>' + tgt.id + '</sub>)');
        }
        return;
      }
      if (ty.kind === 'TyArrow') {
        occurs(srcRef, ty.from);
        occurs(srcRef, ty.to);
      }
    }

    function unify(t1, t2) {
      t1 = force(t1);
      t2 = force(t2);
      if (t1.kind === 'TyBool' && t2.kind === 'TyBool') return;
      if (t1.kind === 'TyVar' && t2.kind === 'TyVar' && t1.ref === t2.ref) return;
      if (t1.kind === 'TyArrow' && t2.kind === 'TyArrow') {
        unify(t1.from, t2.from);
        unify(t1.to, t2.to);
        return;
      }
      if (t1.kind === 'TyVar') {
        occurs(t1.ref, t2);
        t1.ref.link = t2;
        return;
      }
      if (t2.kind === 'TyVar') {
        occurs(t2.ref, t1);
        t2.ref.link = t1;
        return;
      }
      throw new Error('cannot unify ' + formatTy(t1) + ' with ' + formatTy(t2));
    }

    function substitute(ty, subst) {
      if (ty.kind === 'TyVar' && subst.has(ty.ref.id)) return subst.get(ty.ref.id);
      if (ty.kind === 'TyArrow') return { kind: 'TyArrow', from: substitute(ty.from, subst), to: substitute(ty.to, subst) };
      return ty;
    }

    function instantiate(scheme) {
      if (scheme.forall.length === 0) return scheme.type;
      const subst = new Map();
      for (const v of scheme.forall) subst.set(v, freshUnboundVar());
      return substitute(scheme.type, subst);
    }

    function freeMetavars(ty, acc) {
      acc = acc || [];
      ty = force(ty);
      if (ty.kind === 'TyVar' && !acc.some(r => r.id === ty.ref.id)) acc.push(ty.ref);
      if (ty.kind === 'TyArrow') { freeMetavars(ty.from, acc); freeMetavars(ty.to, acc); }
      return acc;
    }

    function gen(ty) {
      const free = freeMetavars(ty);
      const bindable = mode === 'scoped'
        ? free.filter(r => r.scope > state.scope)
        : free.slice();
      return { forall: bindable.map(r => r.id), type: ty };
    }

    function lookup(name) {
      const found = state.env.find(e => e.name === name);
      if (!found) throw new Error("unbound variable: " + name);
      return found.scheme;
    }

    function genLogicDescription(tyRhs, tyGen) {
      if (mode === 'naive') {
        return 'quantify all → ' + formatScheme(tyGen);
      }
      const free = freeMetavars(tyRhs);
      if (free.length === 0) {
        return 'no free vars → ' + formatScheme(tyGen);
      }
      const checks = free.map(r => r.id + '.scope ' + (r.scope > state.scope ? '>' : '≤') + ' current_scope').join(', ');
      return checks + ' → ' + formatScheme(tyGen);
    }

    function infer(exp) {
      depth++;
      let result;
      switch (exp.kind) {
        case 'EBool':
          result = { kind: 'TyBool' };
          emit((exp.value ? 'true' : 'false') + ': Bool', 'EBool');
          break;
        case 'EVar': {
          const scheme = lookup(exp.name);
          result = instantiate(scheme);
          emit(exp.name, 'EVar');
          emitSub('inst (' + formatScheme(scheme) + ') → ' + formatTy(result));
          break;
        }
        case 'ELam': {
          const tyParam = freshUnboundVar();
          state.env.unshift({ name: exp.param, scheme: { forall: [], type: tyParam } });
          emit(formatExp(exp), 'ELam');
          const tyBody = infer(exp.body);
          state.env.shift();
          result = { kind: 'TyArrow', from: tyParam, to: tyBody };
          emit(': ' + formatTy(result));
          break;
        }
        case 'ELet': {
          emit(formatExp(exp), 'ELet');
          state.scope++;
          if (mode === 'scoped') emitSub('enter_scope(): current_scope = ' + state.scope);
          const tyRhs = infer(exp.rhs);
          state.scope--;
          if (mode === 'scoped') emitSub('leave_scope(): current_scope = ' + state.scope);
          const tyGen = gen(tyRhs);
          state.env.unshift({ name: exp.id, scheme: tyGen });
          emitSub('gen ' + formatTy(tyRhs), mode);
          events.push({
            depth: depth + 2,
            text: genLogicDescription(tyRhs, tyGen),
            tag: '',
            kind: mode,
            state: snapshot(),
          });
          const tyBody = infer(exp.body);
          state.env.shift();
          result = tyBody;
          emit(': ' + formatTy(result));
          break;
        }
        case 'EApp': {
          emit(formatExp(exp), 'EApp');
          const tyFn = infer(exp.fn);
          const tyArg = infer(exp.arg);
          result = freshUnboundVar();
          const tyArr = { kind: 'TyArrow', from: tyArg, to: result };
          emitSub('unify ' + formatTy(tyFn) + ' with ' + formatTy(tyArr));
          unify(tyFn, tyArr);
          emit(': ' + formatTy(result));
          break;
        }
      }
      depth--;
      return result;
    }

    try {
      const result = infer(program);
      depth = 0;
      emit('Program: ' + formatTy(result));
    } catch (e) {
      events.push({ depth: 0, text: e.message, tag: '', kind: 'error', state: snapshot() });
    }

    return events;
  }

  let state = { events: [], currentIndex: -1, mode: 'scoped', source: null };

  function render() {
    if (state.events.length === 0) {
      traceEl.hidden = true;
      backBtn.disabled = true;
      stepBtn.disabled = true;
      resetBtn.disabled = true;
      return;
    }
    traceEl.hidden = false;
    while (traceEl.firstChild) traceEl.removeChild(traceEl.firstChild);

    for (let i = 0; i <= state.currentIndex; i++) {
      const ev = state.events[i];
      const row = document.createElement('div');
      row.className = 'lg-trace-row';
      if (i === state.currentIndex) row.classList.add('lg-trace-row-current');
      if (ev.kind === 'naive') row.classList.add('lg-trace-row-naive');
      else if (ev.kind === 'scoped') row.classList.add('lg-trace-row-scoped');
      else if (ev.kind === 'error') row.classList.add('lg-trace-row-error');

      const tag = document.createElement('span');
      tag.className = 'lg-trace-tag';
      tag.textContent = ev.tag || '';
      row.appendChild(tag);

      for (let d = 0; d < ev.depth; d++) {
        const guide = document.createElement('span');
        guide.className = 'lg-trace-guide';
        row.appendChild(guide);
      }

      const desc = document.createElement('span');
      desc.className = 'lg-trace-desc';
      desc.innerHTML = ev.text;
      row.appendChild(desc);

      if (state.mode === 'scoped') {
        const scope = document.createElement('sup');
        scope.className = 'lg-trace-scope lg-scope-' + ev.state.scope;
        scope.textContent = String(ev.state.scope);
        row.appendChild(scope);
      }

      const metavars = document.createElement('span');
      metavars.className = 'lg-trace-metavars';
      if (ev.state.metavars.length > 0) {
        ev.state.metavars.forEach((r, idx) => {
          if (idx > 0) metavars.appendChild(document.createTextNode(', '));
          const chip = document.createElement('span');
          if (state.mode === 'scoped') {
            chip.className = 'lg-scope-' + r.scope + (r.link ? ' lg-metavar-linked' : '');
            chip.textContent = r.link ? r.id + ' ↦ ' + r.link : r.id + ': ' + r.scope;
          } else {
            chip.className = r.link ? 'lg-metavar-linked' : '';
            chip.textContent = r.link ? r.id + ' ↦ ' + r.link : r.id;
          }
          metavars.appendChild(chip);
        });
      }
      row.appendChild(metavars);

      const env = document.createElement('span');
      env.className = 'lg-trace-env';
      if (ev.state.env && ev.state.env.length > 0) {
        env.textContent = ev.state.env.map(e => e.name + ': ' + e.scheme).join(', ');
      }
      row.appendChild(env);

      traceEl.appendChild(row);
    }

    const currentRow = traceEl.querySelector('.lg-trace-row-current');
    if (currentRow) currentRow.scrollIntoView({ block: 'nearest' });
    backBtn.disabled = state.currentIndex <= 0;
    stepBtn.disabled = state.currentIndex >= state.events.length - 1;
    resetBtn.disabled = false;
  }

  function handleSubmit() {
    errorEl.textContent = '';
    let program;
    try {
      program = parse(textarea.value);
    } catch (e) {
      errorEl.textContent = e.message;
      return;
    }
    state.source = textarea.value;
    state.events = runInference(program, state.mode);
    state.currentIndex = state.events.length > 0 ? 0 : -1;
    textarea.disabled = true;
    submitBtn.disabled = true;
    errorEl.hidden = true;
    render();
  }

  function handleStep() {
    if (state.currentIndex >= state.events.length - 1) return;
    state.currentIndex++;
    render();
  }

  function handleBack() {
    if (state.currentIndex <= 0) return;
    state.currentIndex--;
    render();
  }

  function handleReset() {
    state.events = [];
    state.currentIndex = -1;
    state.source = null;
    textarea.disabled = false;
    submitBtn.disabled = false;
    errorEl.textContent = '';
    errorEl.hidden = false;
    render();
  }

  function handleModeChange(newMode) {
    state.mode = newMode;
    if (state.source) {
      let program;
      try { program = parse(state.source); } catch (e) { return; }
      const oldIndex = state.currentIndex;
      state.events = runInference(program, newMode);
      state.currentIndex = Math.min(oldIndex, state.events.length - 1);
      render();
    }
  }

  submitBtn.addEventListener('click', handleSubmit);
  stepBtn.addEventListener('click', handleStep);
  backBtn.addEventListener('click', handleBack);
  resetBtn.addEventListener('click', handleReset);
  naiveRadio.addEventListener('change', () => { if (naiveRadio.checked) handleModeChange('naive'); });
  scopedRadio.addEventListener('change', () => { if (scopedRadio.checked) handleModeChange('scoped'); });

  function resetToInitial() {
    state = { events: [], currentIndex: -1, mode: scopedRadio.defaultChecked ? 'scoped' : 'naive', source: null };
    textarea.value = textarea.defaultValue;
    textarea.disabled = false;
    naiveRadio.checked = naiveRadio.defaultChecked;
    scopedRadio.checked = scopedRadio.defaultChecked;
    submitBtn.disabled = false;
    errorEl.textContent = '';
    errorEl.hidden = false;
    render();
  }

  resetToInitial();
  window.addEventListener('pageshow', (e) => { if (e.persisted) resetToInitial(); });
})();
