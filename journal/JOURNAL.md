# Target journal: Theoretical Computer Science

| Item | Details |
|---|---|
| Journal | Theoretical Computer Science |
| Publisher | Elsevier |
| ISSN | 0304-3975 (print), confirmed in the Crossref journal record; 1879-2294 (electronic), from a secondary listing, not confirmed |
| Homepage | https://www.sciencedirect.com/journal/theoretical-computer-science |
| Submission | Editorial Manager, https://www.editorialmanager.com/tcs/ (also reached by "Submit your article" on the homepage) |
| Template | Elsevier `elsarticle` class (version 3.5, included as `paper/elsarticle.cls`), `preprint,12pt` option, numbered references |

## Scope fit

Combinatorics on words is part of the journal's scope, and the closest prior
work on the number of abelian squares in a word appeared there:

- G. Fici, F. Mignosi, J. Shallit, Abelian-square-rich words, Theoret. Comput.
  Sci. 684 (2017) 29-42, doi:10.1016/j.tcs.2017.02.012.

The present paper settles Conjecture 0.6 of J. Simpson, "Solved and unsolved
problems about abelian squares" (arXiv:1802.04481), on the minimum number of
distinct abelian squares in a binary circular word: the minimum is
floor((n-1)/2), part (a) holds, and the list of extremal words in part (b)
misses (ab)^{n/2} for n = 2 (mod 4), n >= 6.

## Length and format

- The manuscript is 10 pages in the `elsarticle` preprint layout (12 pt, single
  column), with a three-sentence abstract.
- Elsevier accepts a first submission as a single PDF
  (`dist/simpson-abelian-squares.pdf`); after acceptance the LaTeX source and
  the class file are uploaded. `dist/simpson-abelian-squares-tex.zip` and the
  arXiv tarball `dist/simpson-abelian-squares-arxiv.tar.gz` contain exactly
  these two files; the references are in the source (`thebibliography`), so no
  `.bib` or `.bbl` file is needed.
- Required front matter, all present: title, author with address and email,
  abstract, keywords, MSC 2020 codes (68R15, 05A05).
- The journal's guide for authors page returned HTTP 403 to the session that
  prepared this file, so any journal-specific page limit, abstract length limit
  or highlights requirement was not read; check the guide before submitting.
- Editorial Manager asks at submission for a declaration of competing
  interests and for funding information; these are filled in by the author on
  the submission form.

## Policy on AI assistance (Elsevier generative AI policy for journals)

- AI tools may not be listed as authors or cited as authors.
- Use of AI tools in manuscript preparation is disclosed in a separate section
  titled "Declaration of generative AI and AI-assisted technologies in the
  manuscript preparation process", placed before the references; the statement
  appears in the published article. Elsevier's recommended wording is used in
  `paper/main.tex`.
- Use of AI tools in the research process is described in the paper;
  Section 5 (Formal verification) states how the result was checked.
- The author remains responsible for checking all AI-generated output,
  including references. Every DOI in the bibliography was checked against its
  Crossref record, and the statement of Conjecture 0.6 against the arXiv
  source of Simpson's paper.
- Source: https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals
