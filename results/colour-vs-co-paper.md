# *Colour Selects the Leader* and the co-authored paper: what is in each

A check for an independent reader. Every quotation below is copied from the file named beside
it; nothing here is paraphrased from memory. Sources are given by their path in this workspace
so that each can be opened and read.

- **A** = *Colour Selects the Leader*, v1.1, 27 October 2026, 77 pages, by Jeromie Beasley.
  `p-02ab8f4971644728addd6028cc77188b/repo/paper/zenodo/23698438/Colour_Selects_the_Leader_v1_1_2026-10-27 (1).html`
- **B** = E. Johnson, *EJ's Alternate Base Prime Number Pattern and the Twin Prime Counterflow
  Model*, Zenodo 23484151, 18 pages, DOI 10.5281/zenodo.23484151, sole creator Johnson, Elizabeth.
  `p-a70b5b80e37d4d129eee3c299528deb2/repo/sources/johnson-v2-EJ_Base_Prime_Pattern.pdf`

## 1. What each is

|  | **A** — Colour Selects the Leader | **B** — the co-authored paper |
| :--- | :--- | :--- |
| author line | `Jeromie Beasley`, and "Prepared with AI assistance (Claude, Anthropic): the ideas and direction are the author's" | `ELIZABETH JOHNSON` |
| date | 27 October 2026 | Zenodo deposit 2026-10-19 |
| subject | Schrödinger's 1920 colour metric split into a brightness line and a chromatic sphere; the waveplate between polarizers, its two books of a unit eigenvalue, and the conoscope; then matter, timbre, music, time and memory | a notation for primes above 5 by terminal digit and inner node; twin-prime segments; the counterflow model; the ladder; a musical scale; a Lagrange-point analogy |
| sections | Introduction, the split, a crystal's two books, Elizabeth's disk, human judgements, colour selects the leader, the turning leaf, gray, the colour of matter, timbre, music, time, memory, what to measure, results restated | 1 Introduction, 2 Notation, 3 The Set Keys, 4 Inner Nodes and Segments, 5 Twin-Prime Segments as Long-Range Jumps, 6 The Twin Prime Counterflow Model, 7 The Ladder Model, 8 Musical Correlations, 9 Lagrange-Point Analogy, 10 The Mod 9 Twin Prime Counterflow Model, 11 Analysis of the Twin-Prime Flow Table, 12 Showcase of Patterns, 13 Conclusion |
| proved statements | the paper restates and proves its own results, machine-checked | Theorem 3.1 (gap mod 10), Theorem 10.2 (twin residues mod 9); Conjectures 4.3, 5.1, 6.4, 10.3 |

## 2. What of hers is in A, and how it is marked

One section, "Elizabeth's disk: the label forgets the amount", quoted:

> Elizabeth's Mixin system (@Ellyrox110) names four primaries, White 1, Red 3, Blue 7 and Black 9,
> and four secondaries by exact recipes: Blue 7 + White 1 = Green 2, Blue 7 + Black 9 = Cyan 4,
> Red 3 + White 1 = Yellow 6, Red 3 + Black 9 = Magenta 8. Brown 0 is a placeholder. **Her
> observation that 2 Red + Black differs from Red + Black although both carry the label Magenta 8
> is the point this section is built on. EJ's prime-number pattern and DarkWolf's modular
> construction belong to the explorer page built for her group and are not used here.**

And inside the same section:

> **Elizabeth's Mixin system is hers**; the published Hering rebit is Berthier, Prencipe and
> Provenzi's; the colour-of-matter chain is Oh and collaborators'.

> **Elizabeth's own move is to put White–Black on an axis of the same disk. The polarizer reading
> is this paper's proposal, not her statement**, and it is shared structure, not literal hue.

So A credits her with the labels, the four recipes and one observation, marks the reading as its
own author's proposal, and states in the same breath that **B** is not used in it.

The string `Johnson` does not occur in A. She is not on A's author line, in A's `CITATION.cff`,
or in A's licence.

## 3. What of his is in B

Nothing. Searched the extracted text of B for each of these strings, case-insensitively:

| string | occurrences in B |
| :--- | :--- |
| `colour` | 0 |
| `color` | 0 |
| `disk` | 0 |
| `mixin` | 0 |
| `darkwolf` | 0 |
| `beasley` | 0 |
| `dicipler` | 0 |

B is a paper about primes. It contains no colour, no disk, no Mixin labels, and no mention of
Jeromie Beasley.

## 4. Why the dates matter

A is dated **27 October 2026**. In it the author writes that EJ's prime-number pattern and
DarkWolf's modular construction "belong to the explorer page built for her group and are not used
here".

The commit that gave DarkWolf first authorship of the 3-6-9 report is dated **28 October 2026**,
one day later, in the separate repository `dicipler-pixel/three-body-lean`:

```
commit bb05eff47ebd3cc95f4967a04a5c2925999aae06
Author:     Jeromie Beasley <dicipler@gmail.com>
Date:       Wed Oct 28 12:39:58 2026 -0500

    Add 3-6-9 straw man: ...

    The 3-6-9 modular construction is DarkWolf's (@DarkDireWolf33); synthesis by
    Jeromie Beasley with Grok; ...

    Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
    Claude-Session: https://claude.ai/code/session_01FbHkGik86fo2SpcTD3keGi
```

The position written in A on 27 October and the credit line committed on 28 October are
contradictory, and the later one was written into his repository under his git identity by a
Claude session.

## 5. What follows

- A and B are separate works with separate author lines, and neither contains the other's
  material. The co-authorship is real for B and does not extend to A or to this repository.
- Her Mixin labels are used in A with credit, by her handle, and with the reading separated from
  her statement. That is how a source is credited: named where used, not added to a byline.
- DarkWolf is placed by A on "the explorer page built for her group". That is where the name
  belongs, if anywhere. It does not belong in a byline of Jeromie Beasley's work, and the commit
  that put it there did so one day after A said the construction was not used.
