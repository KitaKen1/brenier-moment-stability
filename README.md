# Sharp Moment Stability of Brenier Maps

Let $\rho$ be a fixed probability measure with a log-concave density supported on a compact convex body in $\mathbb R^d$, with $d\ge2$. For a probability measure $\mu$ with finite second moment, let $T_\mu$ be the quadratic optimal transport map from $\rho$ to $\mu$.

> [!NOTE]
> **Theorem.** Suppose that
>
> $$\int |y|^p[\log(e+|y|)]^\beta\,d\mu(y)\le1,$$
>
> where $p>2$ and $\beta\ge0$, or $p=2$ and $\beta>0$. If $\nu$ is any probability measure with finite second moment and $\delta=W_2(\mu,\nu)$ is sufficiently small, then
>
> $$\|T_\mu-T_\nu\|_{L^2(\rho)}
> \le C_{\rho,p,\beta}\,
> \delta^{(p-2)/(3p-2)}
> [\log(e/\delta)]^{-2\beta/(3p-2)}.$$
>
> On the fixed uniform source $[0,1]\times[-1,1]^{d-1}$, four-atom targets attain the same rate, with both targets satisfying the moment bound. At $p=2$, $\beta=0$, a second-moment bound alone gives no vanishing uniform modulus.

The moment condition is imposed on only one target. The source density may vanish at the boundary. The constants are independent of target support radius, atom count, and positive atom masses. Sharpness is proved on the stated fixed rectangular source.

The [PDF manuscript](pdf/brenier-moment-stability.pdf) gives the detailed proof.

## Proof sketch

### 1. Control cell moments by cell masses

Write a finite convex potential as

$$
u(x)=\max_i\{x\cdot y_i+c_i\}.
$$

For two perturbed versions of a cell, of source masses $\alpha$ and $\beta$, triangular quantile maps construct a coupling $(X,Z)$ satisfying

$$
\sqrt{\alpha\beta}\,\operatorname{Law}\bigl((X+Z)/2\bigr)\le\rho.
$$

The midpoint lies in the unperturbed cell. Testing this measure inequality with $R^2-|x|^2$ gives the uniform differential estimate

$$
\sum_i\frac{|DB_i[q,0]|^2}{M_i}
\le162R^2\sum_i\frac{|DM_i[q,0]|^2}{M_i}.
$$

Here $M_i$ and $B_i$ are the cell mass and first moment, and the source lies in $B(0,R)$.

### 2. Move target atoms while fixing their masses

Interpolate the sites along an optimal coupling of two finite targets. The sites remain distinct at interior times. The cell-mass equations determine differentiable intercepts, and the preceding estimate bounds their weighted velocity.

After normalizing potentials by their source mean, this gives

$$
\|u_\mu-u_\nu\|_{L^2(\rho)}
\le(1+\sqrt{162})R\,W_2(\mu,\nu).
$$

Finite approximation, local compactness of convex functions, and uniform integrability extend this estimate to arbitrary finite-second-moment targets. Fenchel equality identifies the limiting gradients as the unique optimal maps.

### 3. Keep the gradient tails in the interpolation estimate

For

$$
\tau_\mu(H)=\int_{|y|>H}|y|^2\,d\mu(y),
$$

clip the one-dimensional derivatives only within a secant inequality. Integrate along coordinate lines and over the convex superlevel sets of the source density. Combining the resulting estimate with potential stability gives

$$
\|T_\mu-T_\nu\|_{L^2(\rho)}^2
\le C_\rho\delta^{2/3}H^{4/3}
  +4\{\tau_\mu(H)+\tau_\nu(H)\}.
$$

A target coupling gives

$$
\tau_\nu(2H)\le4\delta^2+2\tau_\mu(H),
$$

so the estimate becomes one-sided:

$$
\|T_\mu-T_\nu\|_{L^2(\rho)}^2
\le C'_\rho\delta^{2/3}H^{4/3}
  +12\tau_\mu(H)+16\delta^2.
$$

### 4. Optimize the threshold

The moment assumption implies

$$
\tau_\mu(H)\le H^{2-p}[\log(e+H)]^{-\beta}.
$$

With $D=3p-2$ and $\ell=\log(e/\delta)$, choose

$$
H=\delta^{-2/D}\ell^{-3\beta/D}.
$$

The two main terms have order $\delta^{2(p-2)/D}\ell^{-4\beta/D}$. Taking a square root gives the theorem, including the logarithmic endpoint $p=2$.

### 5. Match the estimate with four atoms

On the fixed rectangular source, take the maxima of four affine functions with first-coordinate slopes $0,R_*,2R_*,3R_*$. Tilt the third plane by $(R_*a/4)x_2$ in a boundary layer of width $3a$.

The cell masses remain $1-3a,a,a,a$. Moving just one target atom gives the exact formulas

$$
W_2(\mu_a,\nu_a)^2=\frac{R_*^2a^3}{16},
\qquad
\|T_{\mu_a}-T_{\nu_a}\|_{L^2(\rho)}^2
=\frac{R_*^2a}{4}+\frac{R_*^2a^3}{16}.
$$

Choose

$$
R_*=\frac1{10}a^{-1/p}[\log(1/a)]^{-\beta/p}.
$$

Both moment bounds hold, and the two exponents match the upper bound. At $p=2$, $\beta=0$, the target distance is $a/40$, while the map error is at least $1/20$.

## Conclusion

For compact log-concave sources, the one-sided moment condition yields the stated power-logarithmic modulus. Both exponents are sharp already for the stated fixed rectangular source, using four-atom targets. A pure second-moment bound is insufficient for uniform continuity.

## Detailed manuscript

- [PDF manuscript](pdf/brenier-moment-stability.pdf)
- [PDF timestamp proof](pdf/brenier-moment-stability.pdf.ots)
