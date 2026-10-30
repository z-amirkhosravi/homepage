# Wiki Theme

The visual layer of the Math 2.0 wiki: page template, stylesheet, reading script, fonts and banner. The Website project owns these files. The Math Research project's build fetches them at a pinned tag (`theme-v1`, …) and fills the template; it does not edit them. The markup the build must emit is specified in the wiki theme contract and the Coordinator instructions.

## Files

| Path | Purpose |
| --- | --- |
| `page.html` | Page template with slots |
| `assets/wiki.css` | Layout, typography, statements, proofs, Lean formalizations, build logs and source files, search, print |
| `assets/temml.css` | Temml 0.14.0 stylesheet rules, without its font declarations and `\cancelto` mask |
| `assets/wiki.js` | Contents highlighting, search, discussion and proof controls, fitting wide displays |
| `assets/fonts/` | Libertinus Serif, Serif Display, Sans and Math (OFL), Temml prime font (MIT), DejaVu Sans Mono subset (Bitstream Vera licence, `DejaVu-LICENSE.txt`) |
| `assets/banner.jpg` | Banner, linking to the homepage |

The build copies `assets/` to `dist/assets/theme/`. `page.html` links the stylesheets and script with `?v=N`, the theme release number, so browsers fetch new files after a theme update; each release increments it.

## Template Slots

Replace **every occurrence** of each slot; `{{description}}` appears twice. Since `theme-v4`, `{{section}}` is shown once, in the breadcrumb. After filling, no `{{` may remain.

| Slot | Content | Escaped |
| --- | --- | --- |
| `{{title}}` | Front-matter title | yes |
| `{{description}}` | Front-matter description | yes |
| `{{section}}` | Front-matter section | yes |
| `{{root}}` | Relative prefix to the wiki root | — |
| `{{toc}}` | `ol.toc-list` of sections with nested statements | no |
| `{{notice}}` | The article-kind label `div.article-kind`, or empty (since `theme-v4`; in `theme-v3` it held `div.article-notice`) | no |
| `{{controls}}` | `div.reading-controls`, or empty | no |
| `{{article}}` | Rendered article, beginning with its `h1` | no |
| `{{adjacent}}` | `nav.adjacent`, or empty | no |

The article-kind label sits at the right end of a line above the title. The template moves the description and reading controls beneath the article's `h1` with a short inline script. Without scripting they appear just above the title.

## Attribution Markup

| Element | Markup | Position |
| --- | --- | --- |
| Article kind (since `theme-v4`) | `<div class="article-kind" data-article-kind="exposition">Expository</div>` or `data-article-kind="research"` with `Research`; nothing else | `{{notice}}` slot, not the article body |
| Statement citation (since `theme-v5`) | `<span class="statement-citation" data-citation><a href="#ref-…">[1, p. 45]</a></span>` | Last child of `h3.statement-title`, after the title text and a space |
| Proof citation (since `theme-v5`) | `<span class="proof-citation" data-proof-citation><a href="#ref-…">[1, §3]</a></span>` | In the proof's `summary`: after `span.proof-heading` and `span.visually-hidden` |
| Bibliography (since `theme-v5`) | `<ol class="bibliography">` with one `li` per entry, each starting with its `<span id="ref-…"></span>` anchor | Under the article's References heading; the theme prints the `[n]` numbers |

## Lean Formalizations (since `theme-v9`)

The markup is specified in the Lean formalization contract. In brief:

| Element | Markup | Position |
| --- | --- | --- |
| Panel | `<details class="lean" id="lean-<item>" data-lean-for="<item>">` with `summary` → `span.lean-heading` "Lean formalization" and a `span.visually-hidden` naming the item, then `div.lean-body` | Last child of `aside.statement-meta`, only on items with formal content |
| Declaration | `figure.lean-decl` with `figcaption` (role, `code` name, Source link) and `pre.lean-code` → `code` → one `span.ln` per line; keywords `span.k`; identifiers are links | In `div.lean-body`, or inside a `section.lean-entry` |
| Counterpart | `section.lean-entry` with `id="lean-<full declaration name>"` | The one home of a declaration; ids never go on `details` |
| Deeper level | `details.lean-sub` → `summary`, `div.lean-sub-body` (with `lean-deeper` for "Definition as implemented") | Inside a panel |
| Names used | `div.lean-names` → `p.lean-names-head`, `ul` → `li` | After the declarations |
| Checking line | `p.lean-evidence`, ending with the Build log link | Last child of `div.lean-body` |
| Build log | `table.log-table` in `div.article-table`; `details.log-more` → `summary`, `pre.log-transcript` with `span.log-cmd`, `span.log-exit` | `evidence/lean-…html` |
| Source file | `pre.lean-source` → `code` → one `span id="L<n>"` per line, from line 1 | `lean/sources/…html` |
| Conventions | `dl.lean-conventions`: `dt id` with `code`, `dd` with a link to the mathlib declaration | `lean.html` |

Whitespace between line elements (`span.ln`, `span[id^="L"]`) is ignored, so newlines there are allowed. Lean text is set in `--mono` (DejaVu Sans Mono, falling back to Libertinus Math for 𝕜, 𝓝 and similar). Panels contain no prose readings or glosses of the Lean text.

Since `theme-v9` the margin status list `ul.evidence` is no longer styled and must not be emitted.

`theme-v3` placed attribution and proof-source paragraphs (`p.statement-attribution`, `p.proof-source`). They are no longer used and their styles are removed.

## Behaviour

- **Contents:** sticky beside the article and highlighting the entry being read; a closed "On this page" disclosure below 860 px.
- **Displays:** scaled to fit down to 85%, then scrolled sideways with edge shadows.
- **Search:** results from `search-index.json` in a panel under the field; `/` focuses it.
- **Lean panels:** open beside the statement on wide screens (up to 560 px; the contents column steps aside below 1680 px), under it on narrow ones; a fragment link opens the panel and disclosures around its target; only opened panels print.
- **Reading controls:** hide discussion (persisted under `math-wiki-discussion-hidden`), collapse proofs, concise and expanded proofs, fragment links that reveal hidden targets, printing of collapsed proofs.

## Fonts

`LibertinusMath-Regular.woff2` is recompressed from the Libertinus 7.051 OTF (SHA-256 `ded714b0d3808af527438ed7a85f16933133f66a12104c4a83db4cc248888011`). The release's WOFF2 lacks the OpenType MATH table, without which large operators and stretchy delimiters render at text size. The other Libertinus files are the 7.051 release WOFF2s.

`DejaVuSansMono-subset.woff2` is a subset of DejaVu Sans Mono 2.37 (TTF SHA-256 `c805f9436dbc268644c1d9584f01a601a653e028e08fd74b9b949f6cf8304d88`): Basic Latin, Latin-1, Latin Extended-A, Greek, phonetic modifiers, punctuation, super- and subscripts, letterlike symbols, arrows, mathematical operators and symbols, geometric shapes and mathematical alphanumerics present in the font, made with fontTools 4.55.3 with hinting kept.

## Site Links

The navigation is About, Code, Math, linking to `https://z-amirkhosravi.github.io/homepage/` with the paths `about/`, `code/` and `math/`. Since `theme-v10` there is no separate Math 2.0 tab: the wiki belongs to Math, which is marked as the current section on every wiki page. The homepage's Math page links to the wiki at `https://z-amirkhosravi.github.io/homepage/math-2.0/`. The banner links to the homepage.
