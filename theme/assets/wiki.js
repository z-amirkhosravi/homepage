// Wiki reading interface. Owned by the Website project; see theme/README.md.
// Everything here is an enhancement: pages read completely without it.
(() => {
  const root = document.body.dataset.root || '';
  const narrow = window.matchMedia('(max-width: 860px)');

  // Contents: always open beside the article; a closed disclosure on narrow screens.
  const toc = document.querySelector('details.toc');
  if (toc) {
    const fit = () => { toc.open = !narrow.matches; };
    fit();
    narrow.addEventListener('change', fit);
    toc.addEventListener('click', e => { if (narrow.matches && e.target.closest('a')) toc.open = false; });
  }

  // Highlight the contents entry for the section or statement being read.
  const tocLinks = [...document.querySelectorAll('.toc a[href^="#"]')];
  const targets = tocLinks.map(link => document.getElementById(decodeURIComponent(link.getAttribute('href').slice(1)))).filter(Boolean);
  function markCurrent() {
    let current = null;
    for (const target of targets) {
      if (target.offsetParent === null) continue;
      if (target.getBoundingClientRect().top <= 120) current = target; else break;
    }
    for (const link of tocLinks) {
      if (current && link.getAttribute('href') === '#' + current.id) link.setAttribute('aria-current', 'true');
      else link.removeAttribute('aria-current');
    }
  }
  let ticking = false;
  window.addEventListener('scroll', () => {
    if (ticking) return;
    ticking = true;
    requestAnimationFrame(() => { ticking = false; markCurrent(); });
  }, {passive: true});

  // Fit wide displays: scale down to at most 85%, then let them scroll.
  function fitEquations() {
    for (const box of document.querySelectorAll('.equation')) {
      const math = box.querySelector('math');
      if (!math || box.offsetParent === null) continue;
      math.style.fontSize = '';
      // Scaling is not exactly linear (rules and spacing), so refine once.
      for (let scale = 1, pass = 0; pass < 2 && box.scrollWidth > box.clientWidth + 1 && scale > 0.85; pass++) {
        scale = Math.max(0.85, scale * box.clientWidth / box.scrollWidth - 0.005);
        math.style.fontSize = scale.toFixed(3) + 'em';
      }
    }
    // An inline formula that cannot fit on one line scrolls within the line.
    for (const math of document.querySelectorAll('article math:not([display="block"])')) {
      math.classList.remove('too-wide');
      const line = math.parentElement.closest('p, li, td, .statement-body, .proof-body, section, div');
      if (line && math.getBoundingClientRect().width > line.clientWidth + 1) math.classList.add('too-wide');
    }
  }
  document.fonts.ready.then(fitEquations);
  let resizeTimer;
  window.addEventListener('resize', () => { clearTimeout(resizeTimer); resizeTimer = setTimeout(fitEquations, 150); });

  // Search in the strip, using the build's search index.
  const input = document.querySelector('#wiki-search');
  const panel = document.querySelector('.search-panel');
  const list = document.querySelector('#search-results');
  const status = document.querySelector('#search-status');
  let index, loading;
  async function loadIndex() {
    if (index) return index;
    if (!loading) loading = fetch(root + 'search-index.json').then(r => { if (!r.ok) throw Error(); return r.json(); }).then(data => index = data).catch(e => { loading = null; throw e; });
    return loading;
  }
  async function search() {
    const query = input.value.trim();
    list.replaceChildren();
    panel.hidden = !query;
    if (!query) return;
    status.textContent = 'Searching…';
    try {
      const entries = await loadIndex();
      if (input.value.trim() !== query) return;
      const words = query.toLocaleLowerCase().split(/\s+/);
      const matches = entries.map(entry => {
        const text = (entry.title + ' ' + entry.heading + ' ' + entry.text).toLocaleLowerCase();
        const score = words.every(w => text.includes(w)) ? words.reduce((n, w) => n + (entry.heading.toLocaleLowerCase().includes(w) ? 5 : 0) + (entry.title.toLocaleLowerCase().includes(w) ? 2 : 0) + 1, 0) : 0;
        return {entry, score};
      }).filter(x => x.score).sort((a, b) => b.score - a.score).slice(0, 12);
      status.textContent = matches.length ? matches.length + ' matching sections' : 'No matching sections. Try a shorter term.';
      for (const {entry} of matches) {
        const li = document.createElement('li'), a = document.createElement('a'), context = document.createElement('span'), title = document.createElement('strong'), snippet = document.createElement('p');
        a.href = root + entry.url;
        context.textContent = entry.heading === 'Overview' ? 'Article' : entry.title;
        title.textContent = entry.heading === 'Overview' ? entry.title : entry.heading;
        const at = entry.text.toLocaleLowerCase().indexOf(words[0]), start = Math.max(0, at - 50);
        snippet.textContent = (start ? '…' : '') + entry.text.slice(start, start + 190) + (entry.text.length > start + 190 ? '…' : '');
        a.append(context, title, snippet);
        li.append(a);
        list.append(li);
      }
    } catch {
      status.textContent = 'Search could not load. You can still browse using the contents.';
    }
  }
  if (input) {
    input.addEventListener('input', search);
    input.addEventListener('focus', () => { if (input.value.trim()) panel.hidden = false; });
    input.addEventListener('keydown', e => { if (e.key === 'Escape') { input.value = ''; panel.hidden = true; } });
    document.addEventListener('click', e => { if (!e.target.closest('.search')) panel.hidden = true; });
    list.addEventListener('click', e => { if (e.target.closest('a')) panel.hidden = true; });
    document.addEventListener('keydown', e => {
      const editing = e.target.matches('input, textarea, [contenteditable]');
      if (e.key === '/' && !editing && !e.ctrlKey && !e.metaKey && !e.altKey) { e.preventDefault(); input.focus(); }
    });
  }

  // Hide discussion and examples; the choice persists across articles.
  const discussionToggle = document.querySelector('.discussion-toggle');
  let discussionHidden = false;
  function setDiscussion(hidden, persist = true) {
    discussionHidden = hidden;
    document.querySelectorAll('article .discussion').forEach(el => el.hidden = hidden);
    if (discussionToggle) {
      discussionToggle.textContent = hidden ? 'Show discussion' : 'Hide discussion';
      discussionToggle.setAttribute('aria-pressed', String(hidden));
    }
    tocLinks.forEach(link => {
      const target = document.getElementById(decodeURIComponent(link.getAttribute('href').slice(1)));
      link.closest('li').hidden = !!(hidden && target?.closest('.discussion'));
    });
    if (persist) try { localStorage.setItem('math-wiki-discussion-hidden', String(hidden)); } catch {}
    fitEquations();
  }
  if (discussionToggle) {
    try { discussionHidden = localStorage.getItem('math-wiki-discussion-hidden') === 'true'; } catch {}
    setDiscussion(discussionHidden, false);
    discussionToggle.addEventListener('click', () => setDiscussion(!discussionHidden));
  }

  // Concise and expanded presentations of one proof.
  function selectProof(group, level) {
    group.querySelectorAll('[data-proof-level]').forEach(panel => panel.hidden = panel.dataset.proofLevel !== level);
    group.querySelectorAll('input[type="radio"]').forEach(radio => radio.checked = radio.value === level);
    fitEquations();
  }
  document.querySelectorAll('.proof-presentations').forEach(group => {
    const selector = group.querySelector('.proof-selector');
    selectProof(group, 'concise');
    selector.hidden = false;
    selector.addEventListener('change', e => { if (e.target.matches('input[type="radio"]')) selectProof(group, e.target.value); });
  });

  // Collapse or expand every proof.
  const proofToggle = document.querySelector('.proof-toggle');
  if (proofToggle) {
    const proofs = [...document.querySelectorAll('details.proof')];
    const update = () => { proofToggle.textContent = proofs.some(p => p.open) ? 'Collapse proofs' : 'Expand proofs'; };
    proofToggle.addEventListener('click', () => { const open = !proofs.some(p => p.open); proofs.forEach(p => p.open = open); update(); });
    proofs.forEach(p => p.addEventListener('toggle', () => { update(); if (p.open) fitEquations(); }));
  }

  // Reveal the target of a fragment link: its discussion, proof and presentation.
  function revealHash() {
    let id;
    try { id = decodeURIComponent(location.hash.slice(1)); } catch { return; }
    const target = id && document.getElementById(id);
    if (!target) return;
    if (target.closest('.discussion') && discussionHidden) setDiscussion(false);
    const panel = target.dataset.proofTarget ? document.getElementById(target.dataset.proofTarget) : target.closest('[data-proof-level]');
    if (panel) selectProof(panel.closest('.proof-presentations'), panel.dataset.proofLevel);
    for (let p = target.parentElement; p; p = p.parentElement) if (p.tagName === 'DETAILS' && !p.classList.contains('toc')) p.open = true;
    requestAnimationFrame(() => { target.scrollIntoView({block: 'start'}); markCurrent(); });
  }
  window.addEventListener('hashchange', revealHash);
  // Clicking a fragment already in the address bar does not emit hashchange.
  document.addEventListener('click', e => {
    const link = e.target.closest('a[href]');
    if (!link || e.defaultPrevented || e.ctrlKey || e.metaKey || e.shiftKey || e.altKey || link.target === '_blank') return;
    const url = new URL(link.href, location.href);
    if (url.origin === location.origin && url.pathname === location.pathname && url.search === location.search && url.hash === location.hash) setTimeout(revealHash, 0);
  });
  revealHash();
  markCurrent();

  // Print the selected presentation even if its proof is collapsed.
  let closedForPrint = [];
  window.addEventListener('beforeprint', () => {
    closedForPrint = [...document.querySelectorAll('details.proof:not([open])')];
    closedForPrint.forEach(proof => proof.open = true);
  });
  window.addEventListener('afterprint', () => {
    closedForPrint.forEach(proof => proof.open = false);
    closedForPrint = [];
  });
})();
