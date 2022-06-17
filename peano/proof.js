window.onload = () => {
  const styleSheet = document.createElement('style');
  styleSheet.innerText = '.axm {display: none}';
  document.head.appendChild(styleSheet);

  for (const elem of document.getElementsByClassName('axs')) {
    const axs = elem.nextElementSibling;
    const axsHint = document.createElement('span');
    const n = axs.getElementsByClassName('ax').length;
    axsHint.className = 'axs-hint';
    axsHint.style = 'display: none';
    axsHint.innerHTML = ` (+${n})`;;
    axs.parentNode.insertBefore(axsHint, axs);
    let hidden = true;
    elem.onmouseenter = () => { if (hidden) axsHint.style = '' };
    elem.onmouseleave = () => { if (hidden) axsHint.style = 'display: none' };
    elem.onclick = () => {
      hidden = !hidden;
      axsHint.style = hidden ? '' : 'display: none';
      axs.style = hidden ? '' : 'display: inline';
    };
  }

  function select(tgt) {
    const lastSelected = document.getElementsByClassName('selected')[0];
    if (lastSelected) lastSelected.classList.remove('selected');
    document.getElementById(tgt).classList.add('selected');
  }

  (window.onhashchange = () => {
    const tgt = window.location.hash.split('#')[1];
    if (tgt) select(tgt);
  })();

  function wrap(target) {
    const wrapper = document.createElement('div');
    [ ...target.childNodes ].forEach(child => wrapper.appendChild(child));
    target.appendChild(wrapper);
  }

  let graph = [];
  for (const row of document.getElementsByClassName('proof')[0].getElementsByTagName('tr')) {
    const cells = row.getElementsByTagName('td');
    const stepTd = cells[0];
    if (stepTd) {
      for (const cell of cells) wrap(cell);
      let step = {deps: []};
      step.vdeps = step.deps;
      const thmTd = cells[2];
      step.vhtml = step.html = thmTd.innerHTML;
      const inner = thmTd.getElementsByClassName('thm')[0] ||
                    thmTd.getElementsByClassName('ax')[0];
      if (inner) step.vthm = step.thm = inner.innerHTML;
      const rowId = row.id;
      stepTd.onclick = () => select(rowId);
      for (const hyp of cells[1].getElementsByTagName('a')) {
        step.deps.push(parseInt(hyp.innerHTML) - 1);
      }
      graph.push(step);
    }
  }

  function getTr(n) { return document.getElementById(n + 1); }
  function setThm(i, tr, thm) {
    graph[i].vthm = thm;
    const td = tr.children[2].children[0];
    graph[i].vhtml = td.innerHTML = `<a class="thm" href="${thm}.html">${thm}</a>`;
    return td;
  }
  function setHyps(i, tr, deps) {
    graph[i].vdeps = deps;
    tr.children[1].children[0].innerHTML =
      deps.map(n => { return `<a href="#${n+1}">${n+1}</a>`; }).join(', ');
  }
  function restore(i, tr) {
    const td = tr.children[2].children[0];
    graph[i].vhtml = td.innerHTML = graph[i].html;
    graph[i].vthm = graph[i].thm;
    setHyps(i, tr, graph[i].deps);
    return td;
  }

  function unhide(i) {
    let j = i;
    let tr = getTr(j);
    while (true) {
      restore(j, tr);
      j = graph[j].deps[0];
      tr = getTr(j);
      tr.classList.remove('hidden');
      if (graph[j].thm != 'ax_mp') break;
    }
  }

  for (let i = 0; i < graph.length; i++) {
    const g = graph[i];
    if (g.thm == 'ax_mp') {
      let head = g.deps[0];
      let hide = [head];
      let hyps = [g.deps[1]];
      while (graph[head].thm == 'ax_mp') {
        hyps.push(graph[head].deps[1]);
        head = graph[head].deps[0];
        hide.push(head);
      }
      console.log(hyps);
      if (graph[head].deps.length == 0 && graph[head].thm) {
        const tr = getTr(i);
        let td = setThm(i, tr, graph[head].thm);
        const ast = document.createElement("SPAN");
        ast.title = 'ax_mp nodes elided';
        ast.innerHTML = '*';
        ast.onclick = () => unhide(i);
        td.insertAdjacentElement('beforeend', ast);
        setHyps(i, tr, hyps.reverse());
        for (const j of hide)
          getTr(j).classList.add('hidden');
      }
    }
  }
}
