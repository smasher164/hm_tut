(function () {
  const root = document.querySelector('[data-widget="unification-stepper"]');
  if (!root) return;

  const textarea = root.querySelector('.us-textarea');
  const submitBtn = root.querySelector('.us-submit');
  const backBtn = root.querySelector('.us-back');
  const stepBtn = root.querySelector('.us-step');
  const resetBtn = root.querySelector('.us-reset');
  const errorEl = root.querySelector('.us-error');
  const treeEl = root.querySelector('.us-tree');
  const heapEl = root.querySelector('.us-heap');
  const heapSvg = root.querySelector('.us-heap-svg');

  const SVG_NS = 'http://www.w3.org/2000/svg';

  function tokenize(s) {
    const toks = [];
    let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (/\s/.test(c)) { i++; continue; }
      if (c === '(' || c === ')' || c === ',' || c === '=') {
        toks.push({ type: c });
        i++;
        continue;
      }
      if (c === '?') {
        let j = i + 1;
        while (j < s.length && /[A-Za-z0-9_]/.test(s[j])) j++;
        if (j === i + 1) throw new Error("expected name after '?'");
        toks.push({ type: 'metavar', name: s.slice(i + 1, j) });
        i = j;
        continue;
      }
      if (/[A-Za-z_]/.test(c)) {
        let j = i;
        while (j < s.length && /[A-Za-z0-9_]/.test(s[j])) j++;
        toks.push({ type: 'ident', name: s.slice(i, j) });
        i = j;
        continue;
      }
      throw new Error("unexpected character '" + c + "'");
    }
    return toks;
  }

  function parseType(toks, i, metavars) {
    const tok = toks[i];
    if (!tok) throw new Error("expected type, got end of input");
    if (tok.type === 'ident' && tok.name === 'TyBool') {
      return [{ kind: 'TyBool' }, i + 1];
    }
    if (tok.type === 'ident' && tok.name === 'TyArrow') {
      if (toks[i + 1]?.type !== '(') throw new Error("expected '(' after TyArrow");
      const [from, j] = parseType(toks, i + 2, metavars);
      if (toks[j]?.type !== ',') throw new Error("expected ',' in TyArrow");
      const [to, k] = parseType(toks, j + 1, metavars);
      if (toks[k]?.type !== ')') throw new Error("expected ')' to close TyArrow");
      return [{ kind: 'TyArrow', from, to }, k + 1];
    }
    if (tok.type === 'metavar') {
      let ref = metavars.get(tok.name);
      if (!ref) {
        ref = { state: 'unbound', id: tok.name };
        metavars.set(tok.name, ref);
      }
      return [{ kind: 'TyVar', ref }, i + 1];
    }
    if (tok.type === '(') {
      const [t, j] = parseType(toks, i + 1, metavars);
      if (toks[j]?.type !== ')') throw new Error("expected ')' to close group");
      return [t, j + 1];
    }
    throw new Error("unexpected token '" + (tok.name || tok.type) + "'");
  }

  function parseConstraints(text) {
    const constraints = [];
    const metavars = new Map();
    const rawLines = text.split('\n');
    for (let idx = 0; idx < rawLines.length; idx++) {
      const line = rawLines[idx].trim();
      if (line.length === 0) continue;
      try {
        const toks = tokenize(line);
        const [lhs, j] = parseType(toks, 0, metavars);
        if (toks[j]?.type !== '=') throw new Error("expected '=' between types");
        const [rhs, k] = parseType(toks, j + 1, metavars);
        if (k !== toks.length) throw new Error("extra input after constraint");
        constraints.push({ lhs, rhs });
      } catch (e) {
        throw new Error('line ' + (idx + 1) + ': ' + e.message);
      }
    }
    return { constraints, metavars };
  }

  function typeToString(t) {
    if (t.kind === 'TyBool') return 'TyBool';
    if (t.kind === 'TyArrow') return 'TyArrow(' + typeToString(t.from) + ', ' + typeToString(t.to) + ')';
    if (t.kind === 'TyVar') return '?' + t.ref.id;
    return '?';
  }

  let state = null;

  function buildTree(constraints) {
    return constraints.map(c => ({
      lhs: c.lhs,
      rhs: c.rhs,
      status: 'pending',
      children: [],
    }));
  }

  function findNextPending(nodes) {
    for (const n of nodes) {
      if (n.status === 'pending') return n;
      const child = findNextPending(n.children);
      if (child) return child;
    }
    return null;
  }

  function findActive(nodes) {
    for (const n of nodes) {
      if (n.status === 'active' || n.status === 'forced') return n;
      const child = findActive(n.children);
      if (child) return child;
    }
    return null;
  }

  function findParent(roots, target) {
    function walk(nodes) {
      for (const n of nodes) {
        if (n.children.indexOf(target) !== -1) return n;
        const f = walk(n.children);
        if (f) return f;
      }
      return null;
    }
    return walk(roots);
  }

  function hasError(nodes) {
    for (const n of nodes) {
      if (n.status === 'error') return true;
      if (hasError(n.children)) return true;
    }
    return false;
  }

  function force(ty) {
    if (ty.kind === 'TyVar' && ty.ref.state === 'link') return force(ty.ref.target);
    return ty;
  }

  function occurs(srcRef, ty) {
    const t = force(ty);
    if (t.kind === 'TyVar' && t.ref === srcRef) return true;
    if (t.kind === 'TyArrow') return occurs(srcRef, t.from) || occurs(srcRef, t.to);
    return false;
  }

  function typesEqual(t1, t2) {
    if (t1.kind !== t2.kind) return false;
    if (t1.kind === 'TyBool') return true;
    if (t1.kind === 'TyVar') return t1.ref === t2.ref;
    if (t1.kind === 'TyArrow') return typesEqual(t1.from, t2.from) && typesEqual(t1.to, t2.to);
    return false;
  }

  function setStatus(node, newStatus, undo) {
    const prev = node.status;
    node.status = newStatus;
    undo.push(() => { node.status = prev; });
  }

  function spawnChildren(node, children, undo) {
    const prev = node.children;
    node.children = children;
    undo.push(() => { node.children = prev; });
  }

  function linkRef(ref, target, undo) {
    const prevState = ref.state;
    const prevTarget = ref.target;
    ref.state = 'link';
    ref.target = target;
    undo.push(() => {
      ref.state = prevState;
      if (prevTarget === undefined) delete ref.target;
      else ref.target = prevTarget;
    });
  }

  function cascadeAndAdvance(state, finishedNode, undo) {
    let parent = findParent(state.tree, finishedNode);
    while (parent) {
      if (parent.children.every(c => c.status === 'done')) {
        setStatus(parent, 'done', undo);
        parent = findParent(state.tree, parent);
      } else {
        break;
      }
    }
    const nextPending = findNextPending(state.tree);
    if (nextPending) setStatus(nextPending, 'active', undo);
  }

  function dispatchStep(state) {
    const active = findActive(state.tree);
    if (!active) return null;
    const undo = [];
    const t1 = force(active.lhs);
    const t2 = force(active.rhs);

    // When force would do work, surface it as its own step so the reader sees the swap.
    if (active.status === 'active' && (t1 !== active.lhs || t2 !== active.rhs)) {
      setStatus(active, 'forced', undo);
      return undo;
    }

    if (typesEqual(t1, t2)) {
      setStatus(active, 'done', undo);
      cascadeAndAdvance(state, active, undo);
    } else if (t1.kind === 'TyArrow' && t2.kind === 'TyArrow') {
      const children = [
        { lhs: t1.from, rhs: t2.from, status: 'pending', children: [] },
        { lhs: t1.to, rhs: t2.to, status: 'pending', children: [] },
      ];
      spawnChildren(active, children, undo);
      setStatus(active, 'expanded', undo);
      setStatus(children[0], 'active', undo);
    } else if (t1.kind === 'TyVar' || t2.kind === 'TyVar') {
      const tv = t1.kind === 'TyVar' ? t1.ref : t2.ref;
      const other = t1.kind === 'TyVar' ? t2 : t1;
      if (occurs(tv, other)) {
        setStatus(active, 'error', undo);
      } else {
        linkRef(tv, other, undo);
        setStatus(active, 'done', undo);
        cascadeAndAdvance(state, active, undo);
      }
    } else {
      setStatus(active, 'error', undo);
    }
    return undo;
  }

  function renderTree(nodes) {
    const ul = document.createElement('ul');
    ul.className = 'us-tree-list';
    for (const node of nodes) {
      const li = document.createElement('li');

      const row = document.createElement('div');
      row.className = 'us-tree-node us-tree-' + node.status;

      const indicator = document.createElement('span');
      indicator.className = 'us-tree-indicator';
      indicator.textContent = (node.status === 'active' || node.status === 'forced') ? '▸' : ' ';
      row.appendChild(indicator);

      const content = document.createElement('span');
      content.className = 'us-tree-content';
      const useForced = (node.status === 'forced' || node.status === 'expanded');
      const lhsToShow = useForced ? force(node.lhs) : node.lhs;
      const rhsToShow = useForced ? force(node.rhs) : node.rhs;
      content.textContent = typeToString(lhsToShow) + ' = ' + typeToString(rhsToShow);
      row.appendChild(content);

      const status = document.createElement('span');
      status.className = 'us-tree-status';
      if (node.status === 'done') status.textContent = '✓︎';
      else if (node.status === 'error') status.textContent = '✗︎';
      row.appendChild(status);

      li.appendChild(row);

      if (node.children.length > 0) {
        const childrenWrap = document.createElement('div');
        childrenWrap.className = 'us-tree-children';
        childrenWrap.appendChild(renderTree(node.children));
        li.appendChild(childrenWrap);
      }

      ul.appendChild(li);
    }
    return ul;
  }

  function collectTargets(metavars) {
    const out = new Set();
    for (const [, ref] of metavars) {
      if (ref.state === 'link') out.add(ref.target);
    }
    return out;
  }

  function layoutType(ty, positions, targets) {
    const charW = 8.5;
    const lineH = 30;
    const padX = 10;
    const text = typeToString(ty);
    const width = text.length * charW + 2 * padX;
    const height = lineH;
    return {
      width, height,
      render(svg, x, y) {
        const rect = document.createElementNS(SVG_NS, 'rect');
        rect.setAttribute('x', x);
        rect.setAttribute('y', y);
        rect.setAttribute('width', width);
        rect.setAttribute('height', height);
        rect.setAttribute('class', 'us-type-box');
        svg.appendChild(rect);

        let cursor = x + padX;
        function place(t) {
          const startX = cursor;
          if (t.kind === 'TyBool') {
            cursor += 6 * charW;
          } else if (t.kind === 'TyVar') {
            cursor += (1 + t.ref.id.length) * charW;
          } else {
            cursor += 8 * charW;
            place(t.from);
            cursor += 2 * charW;
            place(t.to);
            cursor += charW;
          }
          positions.set(t, { x: startX, y, w: cursor - startX, h: lineH });
        }
        place(ty);

        const tEl = document.createElementNS(SVG_NS, 'text');
        tEl.setAttribute('x', x + padX);
        tEl.setAttribute('y', y + lineH / 2);
        tEl.setAttribute('class', 'us-type-text');
        const tspans = [];
        function emit(t, insideTarget) {
          const mark = insideTarget || targets.has(t);
          if (t.kind === 'TyBool') {
            tspans.push({ text: 'TyBool', target: mark });
          } else if (t.kind === 'TyVar') {
            tspans.push({ text: '?' + t.ref.id, target: mark });
          } else {
            tspans.push({ text: 'TyArrow(', target: mark });
            emit(t.from, mark);
            tspans.push({ text: ', ', target: mark });
            emit(t.to, mark);
            tspans.push({ text: ')', target: mark });
          }
        }
        emit(ty, false);
        for (const { text: chunk, target: mark } of tspans) {
          const span = document.createElementNS(SVG_NS, 'tspan');
          span.textContent = chunk;
          if (mark) span.setAttribute('class', 'us-type-target');
          tEl.appendChild(span);
        }
        svg.appendChild(tEl);
      },
    };
  }

  function appendArrowheadDefs(svg) {
    const defs = document.createElementNS(SVG_NS, 'defs');
    const marker = document.createElementNS(SVG_NS, 'marker');
    marker.setAttribute('id', 'us-arrowhead');
    marker.setAttribute('viewBox', '0 0 10 10');
    marker.setAttribute('refX', '9');
    marker.setAttribute('refY', '5');
    marker.setAttribute('markerWidth', '7');
    marker.setAttribute('markerHeight', '7');
    marker.setAttribute('orient', 'auto-start-reverse');
    const path = document.createElementNS(SVG_NS, 'path');
    path.setAttribute('d', 'M 0 0 L 10 5 L 0 10 z');
    path.setAttribute('class', 'us-arrowhead');
    marker.appendChild(path);
    defs.appendChild(marker);
    svg.appendChild(defs);
  }

  function drawLinkArrow(svg, cellPos, target, cellPositions, structPositions) {
    if (target.kind === 'TyVar') {
      const targetCell = cellPositions.get(target.ref);
      if (!targetCell) return;
      const fx = cellPos.x;
      const fy = cellPos.y - cellPos.r;
      const tx = targetCell.x;
      const ty = targetCell.y - targetCell.r;
      const dx = Math.abs(tx - fx);
      const arcHeight = Math.max(18, dx * 0.4);
      const cx = (fx + tx) / 2;
      const cy = fy - arcHeight;
      const path = document.createElementNS(SVG_NS, 'path');
      path.setAttribute('d', 'M ' + fx + ' ' + fy + ' Q ' + cx + ' ' + cy + ' ' + tx + ' ' + ty);
      path.setAttribute('class', 'us-link-arrow');
      path.setAttribute('marker-end', 'url(#us-arrowhead)');
      svg.appendChild(path);
      return;
    }
    const pos = structPositions.get(target);
    if (!pos) return;
    const tx = pos.x + pos.w / 2;
    const ty = pos.y;
    const fx = cellPos.x;
    const fy = cellPos.y + cellPos.r;
    const line = document.createElementNS(SVG_NS, 'line');
    line.setAttribute('x1', fx);
    line.setAttribute('y1', fy);
    line.setAttribute('x2', tx);
    line.setAttribute('y2', ty);
    line.setAttribute('class', 'us-link-arrow');
    line.setAttribute('marker-end', 'url(#us-arrowhead)');
    svg.appendChild(line);
  }

  function collectStructures(tree) {
    const out = [];
    for (const node of tree) {
      if (node.lhs.kind !== 'TyVar') out.push(node.lhs);
      if (node.rhs.kind !== 'TyVar') out.push(node.rhs);
    }
    return out;
  }

  function renderHeap(metavars, structures) {
    while (heapSvg.firstChild) heapSvg.removeChild(heapSvg.firstChild);
    appendArrowheadDefs(heapSvg);

    const cellW = 56;
    const cellH = 40;
    const labelW = 60;
    const startX = 1 + labelW;
    const cellY = 26;
    const structRowH = 30;

    const memLabel = document.createElementNS(SVG_NS, 'text');
    memLabel.setAttribute('x', 1);
    memLabel.setAttribute('y', cellY + cellH / 2);
    memLabel.setAttribute('class', 'us-section-label');
    memLabel.textContent = 'memory';
    heapSvg.appendChild(memLabel);

    const cellPositions = new Map();
    const structPositions = new Map();

    let x = startX;
    for (const [name, ref] of metavars) {
      const g = document.createElementNS(SVG_NS, 'g');
      g.setAttribute('class', 'us-cell' + (ref.state === 'link' ? ' us-cell-linked' : ''));
      const rect = document.createElementNS(SVG_NS, 'rect');
      rect.setAttribute('x', x);
      rect.setAttribute('y', cellY);
      rect.setAttribute('width', cellW);
      rect.setAttribute('height', cellH);
      g.appendChild(rect);
      const text = document.createElementNS(SVG_NS, 'text');
      text.setAttribute('x', x + cellW / 2);
      text.setAttribute('y', cellY + cellH / 2);
      text.textContent = '?' + name;
      g.appendChild(text);
      heapSvg.appendChild(g);
      cellPositions.set(ref, { x: x + cellW / 2, y: cellY + cellH / 2, r: cellH / 2 });
      x += cellW;
    }
    const cellsRight = x;

    const targets = collectTargets(metavars);
    const structRowY = cellY + cellH + 32;
    const structGap = 28;
    let sx = startX;
    let structMaxBottom = structRowY;

    if (structures.length > 0) {
      const typesLabel = document.createElementNS(SVG_NS, 'text');
      typesLabel.setAttribute('x', 1);
      typesLabel.setAttribute('y', structRowY + structRowH / 2);
      typesLabel.setAttribute('class', 'us-section-label');
      typesLabel.textContent = 'types';
      heapSvg.appendChild(typesLabel);
    }

    for (const struct of structures) {
      const layout = layoutType(struct, structPositions, targets);
      layout.render(heapSvg, sx, structRowY);
      sx += layout.width + structGap;
      structMaxBottom = Math.max(structMaxBottom, structRowY + layout.height);
    }

    for (const [name, ref] of metavars) {
      if (ref.state === 'link') {
        drawLinkArrow(heapSvg, cellPositions.get(ref), ref.target, cellPositions, structPositions);
      }
    }

    const width = Math.max(cellsRight, sx, 240);
    const totalH = Math.max(120, structMaxBottom + 16);
    heapSvg.setAttribute('viewBox', '0 0 ' + width + ' ' + totalH);
    heapSvg.setAttribute('preserveAspectRatio', 'xMinYMin meet');
    heapSvg.setAttribute('height', totalH);
  }

  function render() {
    if (!state) {
      treeEl.hidden = true;
      heapEl.hidden = true;
      return;
    }
    treeEl.hidden = false;
    heapEl.hidden = false;

    while (treeEl.firstChild) treeEl.removeChild(treeEl.firstChild);
    treeEl.appendChild(renderTree(state.tree));

    renderHeap(state.metavars, collectStructures(state.tree));
  }

  function updateButtons() {
    if (!state) {
      submitBtn.disabled = false;
      backBtn.disabled = true;
      stepBtn.disabled = true;
      resetBtn.disabled = true;
      return;
    }
    submitBtn.disabled = true;
    backBtn.disabled = state.trail.length === 0;
    stepBtn.disabled = hasError(state.tree) || findActive(state.tree) === null;
    resetBtn.disabled = false;
  }

  function handleSubmit() {
    errorEl.textContent = '';
    let parsed;
    try {
      parsed = parseConstraints(textarea.value);
    } catch (e) {
      errorEl.textContent = e.message;
      return;
    }
    if (parsed.constraints.length === 0) {
      errorEl.textContent = 'enter at least one constraint';
      return;
    }
    const tree = buildTree(parsed.constraints);
    tree[0].status = 'active';
    state = { tree, metavars: parsed.metavars, trail: [] };
    textarea.disabled = true;
    errorEl.hidden = true;
    updateButtons();
    render();
  }

  function handleReset() {
    state = null;
    textarea.disabled = false;
    errorEl.textContent = '';
    errorEl.hidden = false;
    updateButtons();
    render();
  }

  function handleStep() {
    if (!state) return;
    const undo = dispatchStep(state);
    if (!undo || undo.length === 0) return;
    state.trail.push(undo);
    updateButtons();
    render();
  }

  function handleBack() {
    if (!state || state.trail.length === 0) return;
    const undo = state.trail.pop();
    for (let i = undo.length - 1; i >= 0; i--) undo[i]();
    updateButtons();
    render();
  }

  submitBtn.addEventListener('click', handleSubmit);
  backBtn.addEventListener('click', handleBack);
  stepBtn.addEventListener('click', handleStep);
  resetBtn.addEventListener('click', handleReset);

  // Refresh after a step leaves Back/Step/Reset enabled in HTML; reset them.
  updateButtons();
})();
