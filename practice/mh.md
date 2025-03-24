## Monty Hall Problem

Let’s define the setup:

- The doors are labeled:$\{0, 1, 2\}$
- Let $D \in \{0, 1, 2\}$ be the random variable representing the door hiding the prize.
- The prize is placed uniformly at random:

$$
\mathbb{P}(D = 0) = \mathbb{P}(D = 1) = \mathbb{P}(D = 2) = \frac{1}{3}
$$

- Let $C$ be the door initially chosen by the contestant. Without loss of generality, we assume:

$$
C = 0
$$

- Let $R$ be the door revealed by the host. The host never reveals:
  - the contestant’s door:$R \ne C$
  - the prize door:$R \ne D$

---

### Distribution of the Revealed Door

Before knowing $D$, and given $C = 0$, the revealed door is uniformly distributed among the remaining doors (subject to constraints above):

$$
\mathbb{P}(R = 1) = \mathbb{P}(R = 2) = \frac{1}{2}
$$

Suppose we observe:

$$
R = 2
$$

We want to compute the **posterior probability** that the prize is behind door 1:

$$
\mathbb{P}(D = 1 \mid R = 2)
$$

Using **Bayes’ Theorem**:

$$
\mathbb{P}(D = 1 \mid R = 2) = \frac{\mathbb{P}(R = 2 \mid D = 1) \cdot \mathbb{P}(D = 1)}{\mathbb{P}(R = 2)}
$$

---

### 🔧 Step-by-Step Computation

- Prior:

$$
\mathbb{P}(D = 1) = \frac{1}{3}
$$

- If $D = 1$ and $C = 0$, then the host must reveal $R = 2$:

$$
\mathbb{P}(R = 2 \mid D = 1) = 1
$$

- Marginal probability of reveal:

$$
\mathbb{P}(R = 2) = \frac{1}{2}
$$

Now plug in:

$$
\mathbb{P}(D = 1 \mid R = 2) = \frac{1 \cdot \frac{1}{3}}{\frac{1}{2}} = \frac{2}{3}
$$

---

### Conclusion

Given that:
- You initially picked door 0,
- The host reveals door 2,

Then the probability the prize is behind **door 1** is:

$$
\mathbb{P}(D = 1 \mid R = 2) = \frac{2}{3} \approx 66.7\%
$$

**Switching doors is the optimal strategy.**

## LEAN4 formalization strategy
- Define the set of doors and basic probability.

- Model the problem: define the prize location D, contestant's choice C, revealed door R.

- Express the constraints.

- Compute the posterior probability using Bayes' Theorem.

- Prove that ℙ(D = 1 | R = 2) = 2/3
