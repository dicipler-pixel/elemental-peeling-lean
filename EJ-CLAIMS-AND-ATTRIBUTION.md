# Claims and attribution: Elizabeth Johnson's contributions, November 2026

**Prepared at Elizabeth Johnson's request, 25 November 2026, to be added to this repository as a record — not to
alter anything in it.** It states which claims in the Light Bridge / harmonic-law material are hers and which are
Jeromie Beasley's, so that a reader does not have to guess.

**The evidence base is her chat**, not this repository: she has stated that her material here has been altered and
that the repository is not a reliable record of her work. So nothing below rests on commit dates. Each claim quotes
what she said, and names the file where it landed.

---

## 1. Her claims

Each row: the claim, her words, and where it is written.

| claim | her words | where it landed |
|---|---|---|
| **The Col** — the unit, its name after her mother **Colleen**, and its algebra $\Theta=2C_2E_{\rm ion}$, $\kappa=1/(6C_2R)$, $\Lambda=6C_2Rb$ | *"Col is my mother Colleen"* · *"I generated Col"* | the Col tables; every table that uses the unit |
| **The specific-heat bridge**: $c=E/(m\Delta T)=3R/M$, and $E/T=3R$ read as that law | *"I found specific heat"* | `specific-heat-bridge`; the $E/T=3R$ invariant |
| **Air and pores**: the air as $a=g-2$, pores as its picture | *"I figured out air and pores"* | the air and pore documents |
| **The composition, and its title "The Light Bridge Harmonic Law"** | *"show the full new Law as The Light Bridge Harmonic Law"* | the nine-line law; the four-page paper |
| **One tail, not two poles**: a single index-2 zero; the receiving colour receives only and so cannot be a second zero | *"only 1 pole as a tail because magenta is only a receiver"* | the hairy-ball treatment, part (A) |
| **A conversion is a mechanism** — a ruler is the instance | *"A ruler is literally a conversion… how the hell is it not a mechanism"* | the retraction, and the three defined words |
| **The column-ordered offset** of the one-period-forward rule, 0.766–1.200, reversing at $d^{10}$ and $p^{3}$ | *"the others are measured and only off due to a factor still hidden in the primes. Isolate it and fix it"* | the corrected cells and the bias table |
| **The offset as a calibrated measuring stick**: 5.84% resolution, and the new row judged against that band | *"Since it can't be derived it is the new measuring stick. Check it in that way"* | the stick document and its data |
| **The demand that the exact content be proved**, which produced eleven theorems | *"prove the Law so fully you stop telling me its wrong"* | `law-proved.lean` |
| **The $\kappa$ correction**: a Col is $\kappa$ kelvin, not $\kappa^{-1}$ | *"fix"* | five corrected documents |
| **$b$ is exact in the SI, not an outside input**: $b=hc/(kx)$, $x$ the root of $5=(5-x)e^x$ | *"b is not an outside input… but please check"* | the corrected provenance lines |
| **Her vocabulary** — air, tinder, kindling, firewood, superfluid, firework — labelled framing, never mathematics | stated across her sessions | every document that uses it |

## 2. His claims

Stated without reservation, and relied on:

* **The loop-wall library and everything in it**: the peel coordinate, the reflection coefficient $\Gamma$, the wall
  $z_w=3+2\sqrt2$, the exceptional points, the colour wheel's formalisation, `BridgeUnderdetermination`, and the
  archive certificate.
* **His sharpest negative**, in his own words: *"no 2-jet at $\Gamma=0$ can select the bridge"*.
* **The governance of the work**: `BRIDGE.md`, `COVERAGE.md`, `LIMITATIONS.md`, `PROVENANCE.md`, `AI_USE.md`,
  `README.md`, `CITATION.cff`.
* **The verifier and the archive generator**: `scripts/verify.py`, `scripts/gen_archive_lean.py`,
  `scripts/config.json`.
* **The name "Light Bridge"** — settled by her on 25 November: *"The light bridge name is his."*

## 3. Classical, and therefore neither's

$\lambda T=b$ is Wien (1893); $E/T=3R$ is Dulong–Petit (1819); $\lambda=\Lambda/\Theta$ is the definition of the ruler.
**What is hers is the closure**: that the thermal road, $b/T$, and the rung road, $\Lambda/\Theta$, give one number for
every rung — theorem `thermal_eq_rung`, written at her requirement.

## 4. What she is not claiming

She does not claim the library, the name, the discrete arithmetic's content (the residues modulo 30, $T\equiv2\ (6)$,
the cell rule $(n+l,n)\le(8,7)$, the period-8 count, the fission countdown), or part (K)'s content. Where those appear
in her pages, they are credited as the record's; for the cell rule and part (K) her contribution was to restore them
to the page after they had been dropped.

## 5. What cannot be assigned on any record

The analysis tree — the many files of notes, tables and figures around this work — is committed neither to `main` nor
anywhere else, which is also true of his papers. It was produced in sessions of one shared workspace, and neither
party's history can say who directed which. It is not claimed here in either direction.

## 6. What she is asking

Either of two, his choice:

1. **Credit** — this file, or a line in `AUTHORS.md` or `README.md` naming the claims in §1 as hers and §2 as his.
2. **Removal** — if he prefers her material out of his files, her branch `ej-results` modifies nine of them
   (`.gitignore`, `AI_USE.md`, `AUTHORS.md`, `COVERAGE.md`, `LIMITATIONS.md`, `PROVENANCE.md`, `README.md`,
   `LoopWall/Observer.lean`, `LoopWall/UniformLogRatio.lean`, `scripts/gen_archive_lean.py`), and she will take them
   back out on request.

**And correction in either direction:** if any claim in §1 predates her sessions in his work, naming the earlier file
moves it to §2 and the record will say so. The aim is a record a third party can read without having to guess.
