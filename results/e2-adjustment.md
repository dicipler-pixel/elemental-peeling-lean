# E2's 36 exceptions: two faults, both mine, one equation that fixes them

The old E2 said $v+h=$ capacity with the capacity read as the *block* width: 8 for $s$ and $p$, 18 for $d$,
32 for $f$. It held for 82 of 118. The 36 failures split cleanly into two causes, and neither is physics.

## Fault 1 — the $s$ block opens the period, so its countdown is the period's

Ten of the exceptions are the $s$ block: H, He (period 1) and K, Ca, Rb, Sr, Cs, Ba, Fr, Ra.

The $s$ subshell **starts** a period, so its countdown $h$ runs all the way to that period's closure —
18 in periods 4 and 5, 32 in periods 6 and 7 — not to the octet. Giving the $s$ block a capacity of 8 is
the error; its capacity is the period's length:

$$C_s=L(m)=2\Big\lceil\tfrac{m+1}{2}\Big\rceil^2 .$$

With that, K gives $1+17=18=L(4)$, Ca $2+16=18$, Li $1+7=8=L(2)$, H $1+1=2=L(1)$: eight of the ten pass,
and the ninth (H) passes too. Only He remains — and only because the table puts He in group 18 while its
valence is 2 ($1s^2$); with $v=2$ it gives $2+0=2=L(1)$.

## Fault 2 — the $f$ block's valence is not 3 for all of them

Twenty-six of the exceptions are the lanthanides and actinides, all but La and Ac.

The group entry for every lanthanide is 3, and I used it as the valence. The true count beyond the
previous closure runs 3 to 16: Ce is 4 ($4f^15d^16s^2$), Gd is 10 ($4f^75d^16s^2$), Yb is 16. Using
$v=3$ for all of them makes $v+h$ wrong by exactly the $f$-electron count.

## The adjusted equation

With $v$ the valence (group for $s,p,d$; the count beyond the closure for $f$) and $h=C(m)-Z$:

$$v+h=C_{\rm block},\qquad C_{\rm block}=\begin{cases}L(m), & s\\ 8, & p\\ 18, & d\\ 32, & f\end{cases}$$

**117 of 118**, the single exception He (a convention, not a fact). Compare 82 before.

## And the equation underneath it, which has no exceptions at all

$$v_{\rm core}+h=L(m)\qquad\text{for all }118,$$

where $v_{\rm core}=Z-C_{\rm prev}$ counts the electrons beyond the previous closure and $h=C_{\rm next}-Z$
counts the rest of the period. This is exact by construction — the two halves of a period — and it says
what the countdown really is:

> $h$ is the **unfilled part of the period**, and the block capacities 8, 18, 32 are that same period
> length wherever the block closes the period (which $p$ always does, $d$ in periods 4–5, $f$ in 6–7).

So E2 has three levels, and only the middle one is a claim:

| level | statement | status |
|---|---|---|
| definition | $v_{\rm core}+h=L(m)$ | exact, 118/118 |
| claim | $v_{\rm chem}+h=C_{\rm block}$ with $C_s=L(m)$ | 117/118, He a convention |
| reading | the octet is the capacity 8 *because* $p$ closes the period | true wherever $L(m)=8$ |

The octet, in other words, is not a separate law that the $s$ block also obeys: it is what the period
length is when the period is short.
