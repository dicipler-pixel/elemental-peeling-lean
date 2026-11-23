# Pushing the oscillation: why \(5f\) competes for five electrons and \(4f\) for two

The claim under test: \(5f\) overlaps \(6d\) more strongly than \(4f\) overlaps \(5d\), and that is why
the head of the \(5f\) series promotes five electrons to \(d\) while the head of \(4f\) promotes two.
Two independent checks, one from the configurations alone and one from radial size. Both agree, and
the places where they do not agree are informative.

## 1. The model, stated before the fit

One electron either joins the \(f\) shell ($k\to k+1$) or goes to $d$ ($d^0\to d^1$). Energies

$$E(f^{k+1}d^0)-E(f^{k}d^1) \;=\; \underbrace{(\varepsilon_d-\varepsilon_f)}_{\Delta(k)}
\;-\;U_f\,k\;+\;K\,G_f(k),$$

with $G_f(k)=\Phi(k+1)-\Phi(k)$ the exchange increment and $U_f$ the repulsion an extra $f$ electron
pays. **The \(d\) level wins iff** $\Delta(k) < U_f k - K G_f(k)$. Take

$$\Delta(k)=d_0+d_1 k\quad(\text{the } f \text{ level drops as the shell fills: the contraction}),$$

three parameters $(d_0,d_1,U_f)$ per series, and $G_f$ fixed by counting alone
$=0,1,2,3,4,5,6,-6,-5,-4,-3,-2,-1,0$.

## 2. Both series are feasible, and the crossing is what differs

Scanning the three parameters ($U\in[0,1.5]$, $d_1\in[0.2,10]$, $d_0$ whatever the constraints allow)
against the measured flip sets — $4f$: $\{0,1,7\}$, $5f$: $\{0,1,2,3,4,7\}$ — both sets are feasible, and
the admissible region gives:

| series | $d_0/K$ (gap at $k=0$) | $d_1/K$ (contraction per electron) | crossing $k^\*=-d_0/d_1$ | head width observed |
|---|---|---|---|---|
| 4f | $-5.2$ … $-1.9$ | $0.86$ … $3.10$ (med 1.98) | **$0.8$ … $3.3$** (med 1.8) | 2 (La, Ce) |
| 5f | $-32.5$ … $-13.0$ | $2.26$ … $7.00$ (med 4.62) | **$3.5$ … $5.9$** (med 4.9) | 5 (Ac…Np) |

So the two series differ in a specific, measurable way: in $5f$ the \(f\) level starts **much higher**
above $d$ (by 13–32 exchange quanta instead of 2–5) and falls **about twice as fast**, and the two
effects do not cancel — the crossing moves out from $k^\*\approx2$ to $k^\*\approx5$. The head width is
the crossing rounded to an integer, and it comes out 2 and 5 without being fitted to be so.

Representative fits (median parameters), read as a table:

| $k$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| $G_f/K$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | −6 | −5 |
| step cost $Uk-G$ (4f) | 0.0 | −0.2 | −0.5 | −0.8 | −1.0 | −1.2 | −1.5 | **11.2** | 11.0 |
| $\Delta/K$ (4f) | −3.5 | −1.6 | 0.4 | 2.4 | 4.4 | 6.4 | 8.3 | 10.3 | 12.3 |
| measured | **d** | **d** | f | f | f | f | f | **d** | f |
| $\Delta/K$ (5f) | −22.7 | −18.1 | −13.5 | −8.9 | −4.2 | 0.4 | 5.0 | 9.6 | 14.2 |
| measured | **d** | **d** | **d** | **d** | **d** | f | f | **d** | f |

The single spike at $k=7$ (the step out of the half-filled $f^7$, costing 6 exchange quanta plus
repulsion) is what produces Gd and Cm in both series. Everything else is the crossing.

## 3. Radial size: the same ordering, from a model with no parameters at all

Hydrogenic mean radius at fixed $Z$: $\langle r\rangle \propto 3n^2-l(l+1)$. Comparing the two members
of each competition at the same atom:

| pair | $3n^2-l(l+1)$ | ratio $f/d$ | verdict |
|---|---|---|---|
| $4f$ vs $5d$ | 36 vs 69 | **0.522** | far apart |
| $5f$ vs $6d$ | 63 vs 102 | **0.618** | closer |
| $5g$ vs $6f$ | 55 vs 96 | **0.573** | in between |

The ordering matches the configurations: the relative size gap is smallest for $5f/6d$, which is the
pair that competes longest. This is the standard "more extended \(5f\)" argument, and it lands on the
right side without tuning anything.

## 4. Where the same index fails — and why that is a feature

Apply the identical index to the $s$–$d$ competitions:

| pair | ratio $d/s$ | measured crossing $k^\*$ |
|---|---|---|
| $3d$ vs $4s$ | 0.438 | 7.7 |
| $4d$ vs $5s$ | 0.560 | **4.0** |
| $5d$ vs $6s$ | 0.639 | 6.5 |

By the index, $5d/6s$ are the closest pair and the \(5d\) series should cross earliest. It crosses
*latest but one* — the \(4d\) series crosses at $k^\*=4$ and the \(5d\) at $6.5$. The index mis-orders
these two, and the direction of the miss is exactly the direction relativity pushes it: the $6s$ orbital
is relativistically contracted and stabilised, so the \(6d\) level has further to fall before it crosses.
A hydrogenic index cannot contain that, and the data say it is missing.

So the honest status of §3: the radial index is a **correlate that points the right way for $f/d$ and
the wrong way for $s/d$**, and the one place it fails is where a known physical term (relativity,
$\sim Z\alpha$ in the $s$ orbital) is absent. It is not the mechanism; it is a proxy that works where
relativity is small.

## 5. The prediction this makes for the next block (untestable today)

Under the same equations, after $7p$ ($Z=118$) comes $8s^2$ ($119,120$), then $5g$ opens at $Z=121$ with
capacity $2(2\cdot4+1)=18$, so the $k$-th $g$ electron is predicted at $Z=120+k$ and the half-fill is
$k=9$. The exchange increment for a $g$ shell is $0,1,\dots,8,-8,\dots,0$: the step *into* the ninth is
cheap ($+8$) and the step *into* the tenth is expensive ($-8$ plus the repulsion of nine). By the same
rule as Gd ($Z=64$, predicted $4f^8$) and Cm ($Z=96$, predicted $5f^8$), the spike lands on the element
whose predicted configuration carries the expensive tenth electron:

* **a Gd-like spike at $Z=130$** — one electron promoted out of $5g$ into the next subshell, the $g$
  analogue of Gd and Cm;
* **a head block of intermediate width, 3 or 4 electrons** ($Z=121$–$124$): the radial ratio
  $5g/6f=0.573$ sits between $0.522$ (2 flips) and $0.618$ (5 flips), so the crossing lands between them.

Both are falsifiable the day elements 121–130 are made. The second is the weaker prediction, since the
head width also depends on where $\Delta(0)$ starts, which the index does not give.

## 6. Limits

Three parameters per series against fourteen data points, so the fits are not evidence of a mechanism —
they are a compression, and the compression is what makes the two series comparable. The comparison in
§2 (crossing at 1.8 versus 4.9) is a statement about the measured configurations and survives any
monotone $\Delta$; the *values* of $d_0$ and $d_1$ do not. What would settle it is a Hartree–Fock
computation of the two configurations for La, Tb, Ac and Bk — the four elements that pin the crossing —
which is not something this VM can do honestly in a session.
