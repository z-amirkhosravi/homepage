# Wiki Theme

The visual layer of the Math 2.0 wiki: page template, stylesheet, reading script, fonts and banner. The Website project owns these files. The Math Research project's build fetches them at a pinned tag (`theme-v1`, …) and fills the template; it does not edit them. The markup the build must emit is specified in the wiki theme contract and the Coordinator instructions.

## Files

| Path | Purpose |
| --- | --- |
| `page.html` | Page template with slots |
| `assets/wiki.css` | Layout, typography, statements, proofs, search, print |
| `assets/temml.css` | Temml 0.14.0 stylesheet rules, without its font declarations and `\cancelto` mask |
| `assets/wiki.js` | Contents highlighting, search, discussion and proof controls, fitting wide displays |
| `assets/fonts/` | Libertinus Serif, Serif Display, Sans and Math (OFL), Temml prime font (MIT) |
| `assets/banner.jpg` | Banner, linking to the homepage |

The build copies `assets/` to `dist/assets/theme/`.

## Template Slots

Replace **every occurrence** of each slot; `{{section}}` and `{{description}}` appear twice. After filling, no `{{` may remain.

| Slot | Content | Escaped |
| --- | --- | --- |
| `{{title}}` | Front-matter title | yes |
| `{{description}}` | Front-matter description | yes |
| `{{section}}` | Front-matter section | yes |
| `{{root}}` | Relative prefix to the wiki root | — |
| `{{toc}}` | `ol.toc-list` of sections with nested statements | no |
| `{{notice}}` | `div.article-notice`, or empty (since `theme-v3`) | no |
| `{{controls}}` | `div.reading-controls`, or empty | no |
| `{{article}}` | Rendered article, beginning with its `h1` | no |
| `{{adjacent}}` | `nav.adjacent`, or empty | no |

The template moves the description, article notice and reading controls beneath the article's `h1` with a short inline script. Without scripting they appear just above the title.

## Attribution Markup (since `theme-v3`)

| Element | Markup | Position |
| --- | --- | --- |
| Article notice | `<div class="article-notice" data-article-kind="exposition\|research">` containing the existing notice paragraphs | `{{notice}}` slot |
| Statement attribution | `<p class="statement-attribution" data-origin="…"><span class="statement-attribution-label">Attribution.</span> …</p>` | In `div.statement`, after `h3.statement-title`, before `div.statement-body` |
| Proof source | `<p class="proof-source"><span class="proof-source-label">Proof source.</span> …</p>` | First child of `div.proof-body` |

## Behaviour

- **Contents:** sticky beside the article and highlighting the entry being read; a closed "On this page" disclosure below 860 px.
- **Displays:** scaled to fit down to 85%, then scrolled sideways with edge shadows.
- **Search:** results from `search-index.json` in a panel under the field; `/` focuses it.
- **Reading controls:** hide discussion (persisted under `math-wiki-discussion-hidden`), collapse proofs, concise and expanded proofs, fragment links that reveal hidden targets, printing of collapsed proofs.

## Fonts

`LibertinusMath-Regular.woff2` is recompressed from the Libertinus 7.051 OTF (SHA-256 `ded714b0d3808af527438ed7a85f16933133f66a12104c4a83db4cc248888011`). The release's WOFF2 lacks the OpenType MATH table, without which large operators and stretchy delimiters render at text size. The other Libertinus files are the 7.051 release WOFF2s.

## Site Links

The navigation links to `https://z-amirkhosravi.github.io/homepage/` with the paths `code/`, `math/`, `math-2/` and `about/`. These are provisional until the redesigned homepage is built.
