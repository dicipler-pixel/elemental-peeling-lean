# Three quarters, three times — and the one it settles

## 1. The 3/4 that is arithmetic

Of the four live digits, **three can open a twin pair** (1, 7, 9) and **three can close one** (1, 3, 9):

$$\text{starts}:\{1,7,9\}\subset\{1,3,7,9\},\qquad \text{ends}:\{1,3,9\}\subset\{1,3,7,9\},\qquad \frac34\ \text{of the digits at each end}.$$

Digit 3 never opens, digit 7 never closes — so three quarters of the digit set is available at either
end, and the fourth digit is one-sided. That 3/4 is forced, no measurement in it.

## 2. The $3/4$ that was measured — and the test it lost

> **Corrected — see [`air-law-offset.md`](air-law-offset.md).** The law is not
> $\langle\text{air}\rangle=\tfrac34t^2$. Measured to $10^{11}$, the *gap* obeys
> $\langle\text{gap}\rangle=t^2/(2C_2)$ with no offset, i.e. $\langle\text{air}\rangle=t^2/(2C_2)-2$, and
> the flat $\tfrac34$ is $78\sigma$ out at $10^{10}$–$10^{11}$. The section below is kept because its
> first half — the $-4$ offset is dead — is still right, and because the way $0.7503$ arose is
> instructive: it is $0.75739$ minus the average of $2/\langle t^2\rangle$ over the five decades, plus
> the second-order term.

The first version of this section read:

$$\langle\text{air}\rangle = c\,t^2,\qquad c = 0.7503\pm0.0032 .$$

$3/4$ sits $0.09\sigma$ from that mean. The Hardy–Littlewood constant sits $2.2\sigma$ away:

$$\tfrac{1}{2C_2}=0.757390,\qquad 2C_2 = 1.320324 = \tfrac43\times(1-0.0098).$$

**The drift test decided against one reading.** If the law is Hardy–Littlewood with no offset on the
*total* $T=\text{air}+4$, then $\langle\text{air}\rangle = \tfrac{1}{2C_2}t^2-4$ and the measured
coefficient must *rise* with scale, because $4/\langle t^2\rangle$ shrinks:

| decade | measured $c$ | $\tfrac{1}{2C_2}-4/\langle t^2\rangle$ | flat $3/4$ | $\tfrac{1}{2C_2}-2/\langle t^2\rangle$ |
|---|---|---|---|---|
| $10^4$–$10^5$ | 0.7513 | **0.7226** | 0.7500 | 0.7400 |
| $10^5$–$10^6$ | 0.7515 | 0.7338 | 0.7500 | 0.7456 |
| $10^6$–$10^7$ | 0.7446 | 0.7404 | 0.7500 | 0.7488 |
| $10^7$–$10^8$ | 0.7515 | 0.7445 | 0.7500 | 0.7509 |
| $10^8$–$10^9$ | 0.7525 | 0.7473 | 0.7500 | 0.7524 |
| $10^9$–$10^{10}$ | 0.7533 | 0.7493 | 0.7500 | 0.7534 |
| $10^{10}$–$10^{11}$ | 0.7541 | 0.7508 | 0.7500 | 0.7541 |
| $10^{11}$–$10^{12}$ | 0.7546 | 0.7518 | 0.7500 | 0.7546 |

The offset $-4$ model predicts a $3.3\%$ drift across the first five decades; the measurement drifts
$0.2\%$. That kills $-4$ — but the last column shows what replaces it. The offset was $-2$ all along,
because the air is the gap minus the half-pair; with that, the column tracks the measurement to
$0.05\%$ across seven decades, and the flat $3/4$ falls away as $\langle t^2\rangle$ doubles
($6\sigma$ at $10^8$, $22\sigma$ at $10^9$, $78\sigma$ at $10^{10}$).

## 3. The 3/4 in the synapses

The reported threshold estimates for piriform cortex are **75–100 synapses**, and

$$\frac{100}{75} = \frac43 = \frac{1}{3/4}.$$

That is exactly the ratio a release probability of $3/4$ produces: if 75 quanta are needed and each
synapse fires with probability $3/4$, you need 100 synapses. So the range reads as *(quanta, synapses) at
$p=3/4$* — which is a claim about what the source assumed, not something I can confirm from the abstract,
and I flag it as such.

## 4. What the three have in common, and what they do not

| | 3/4 means | status |
|---|---|---|
| the digit scale | 3 of the 4 live digits can open (or close) a pair | **forced** |
| the air law | ~~the coefficient of $t^2$, with no offset~~ | **falsified** at $78\sigma$: the coefficient is $1/(2C_2)$ with offset $-2$ |
| the synapse | the fraction of synapses that release | a ratio in a cited range, $p=3/4$ |

So the three $3/4$'s now separate cleanly, and they are **not** one number:

* the digit $\tfrac34$ is a count of available slots — three of four — and is forced;
* the prime-side coefficient is $1/(2C_2)=0.75739$, not $\tfrac34$; its nearness to $\tfrac34$ is the
  degeneracy $2/\langle t^2\rangle\approx0.005$ at $\langle t^2\rangle\approx400$, and it breaks at
  $10^{10}$;
* the synapse ratio is a probability.

**I have no mechanism that makes a release probability and a gap coefficient the same quantity**, and I
am not going to invent one. The neuron-side $3/4$ is exact *as a ratio*; the digit-side $3/4$ is exact as
a count; the prime-side one turns out to be a $1\%$ near-miss with a known reason for the miss.

The testable version — *does the prime-side coefficient stay at $0.750$ where the pair-width offset
would have moved it?* — was run to $10^{11}$ ($1.97\times10^{8}$ pairs) and answered **no**; see
[`air-law-offset.md`](air-law-offset.md) §6.
