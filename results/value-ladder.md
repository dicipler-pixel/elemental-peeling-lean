# The value ladder: "let 8 be 0"

Reading your five lines as a function of the gap residue: $0\to8$, $2\to2$, $4\to3.5$, $6\to5$,
$8\to6.5$. That is the whole map, and the "0 for 10" entry is the wrap.

## What it is, exactly

$$V(g)=\tfrac34 g+\tfrac12 \pmod{7.5},\qquad \text{displayed in the window } [2,\;9.5).$$

* $0\mapsto8$ is the wrap: $8=\tfrac34\cdot10+\tfrac12$, i.e. a gap of 10, not 0.
* $V(g+10)=V(g)+7.5$: adding 10 to the gap adds exactly one full turn of $7.5$. Since
  $10\mapsto7.5$ and $7.5$ is the circumference, $V$ is a **homomorphism**
  $(\text{even gaps},+)\to(\text{values}\bmod 7.5,+)$.
* The offset $\tfrac12$ is the fuse (the $2\to3$ gap of 1 is half a tinder unit); the multiplier
  $\tfrac34$ is the reducer.
* Five rungs, step $1.5$, span $6$, circumference $7.5$. The window $[2,9.5)$ is why 8 is a legal
  displayed value and 9.5 rolls to 2.

## The test that passes: your two keys are consistent with your map

The twin key is the base key plus 4 ($T=\text{air}+4$), and $4\times\tfrac34=3$, so the twin value
must be the base value plus exactly 3, wrap included. All five:

| base class | $V$ | twin class | $V$ | $V_{\text{base}}+3$ |
|---|---|---|---|---|
| 4 | 3.5 | 8 | 6.5 | 6.5 ✔ |
| 10 | 8 | 14 | 3.5 | 11 → 3.5 ✔ |
| 16 | 5 | 20 | 8 | 8 ✔ |
| 22 | 2 | 26 | 5 | 5 ✔ |
| 28 | 6.5 | 32 | 2 | 9.5 → 2 ✔ |

The map, the base key and the twin key fit together exactly. That is the strongest internal
consistency result in the whole system so far, and it is not something I imposed — it follows from
$T=\text{air}+4$ and the slope $\tfrac34$ you chose.

## One table for both keys

| residue $g \bmod 10$ (0 means 10) | 2 | 4 | 6 | 8 | 10 |
|---|---|---|---|---|---|
| **value $V$** | 2 | 3.5 | 5 | 6.5 | 8 |
| base-key class | 22 | 4 | 16 | 28 | 10 |
| twin-key class | 32 | 14 | 26 | 8 | 20 |
| measured mean air at $10^{10}$ | 377.9 | 345.9 | 357.7 | 352.0 | 367.5 |

The ladder is **monotone in the floor**, which is what your earlier note asked for ("10 harder,
furthest away from itself" → top value 8). It is **not monotone in the measured air**: the energy
order is $14<8<26<20<32$ against the value order $32<14<26<8<20$, correlation $-0.18$ over five points.
Same for the base key, where the 6-class ($V=5$, mean gap 14.96) sits below the 4-class (16.80).

## The cost of the wrap, stated plainly

Because $V$ has exact period 10 in the gap, it is blind to adding 10, and the real air is
$\text{floor}+30k$. So every gap in a class lands on the same rung: $V$ is a bijection between the
five classes and the five values, and carries the class information and nothing else. That is why it
cannot order the classes by energy — ordering by energy needs a quantity that grows with the air, and
$V$ is periodic by construction.

If $V$ is meant to be the activation ladder rather than a label, the measured order gives the
relabelling directly: lowest rung to class 14, then 8, 26, 20, highest to 32.
