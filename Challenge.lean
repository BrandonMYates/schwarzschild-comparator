/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Challenge: exact solutions of the Einstein equations, verified in coordinates

This file is the human-auditable statement. It imports only Mathlib.

**The compared set is exactly the theorems stated in this file.** Nothing outside it is claimed.

## Why this entry exists — read this first

The compared statements are **classical**. Schwarzschild's metric and its vacuum property date
to 1916, the `Λ` generalisation to Kottler in 1918, and the uniqueness statement to Jebsen
(1921) and Birkhoff (1923). **No new mathematics is claimed here, and none should be read into
this entry.**

The point of checking them is the *definitions*. Mathlib contains no curvature of any kind
(grepped, below), so every definition in Part I had to be written from scratch: a sign
convention, an index convention, a contraction convention, and a computational method —
explicit component calculation with the lapse and its derivatives carried as symbolic atoms.
Each of those could be wrong in a way no amount of Lean type-checking would detect, because
Lean checks that a proof establishes a statement, not that a definition means what its name
says. This entry certifies them the only way they can be certified: by computing textbook
solutions with them and getting the textbook answers — including a *nonvanishing* answer in
Part IV, which fixes the overall sign of the curvature convention and rules out the possibility
that `ricci` is accidentally identically zero. Independently of Lean, the definitional surface
was cross-checked against a symbolic computer-algebra computation before any proof was tried.

So this is a **proof of concept**, stated as such, and its purpose is forward-looking: later
work in this programme — junction conditions, thin shells, sourced solutions — is intended to be
stated against *these same definitions*, which a reader can then trust because they were first
certified here against solutions whose answers are already known.

## The objects

Everything is a computation in one fixed coordinate chart, an open subset of `ℝ⁴`. A metric is a
matrix-valued function `g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ`; the physical case is `n = 4`
with coordinates `x 0 = t`, `x 1 = r`, `x 2 = θ`, `x 3 = φ`, signature `(−,+,+,+)`, `G = c = 1`.

Part I defines the whole curvature chain — coordinate partial derivative, Christoffel symbols,
Riemann tensor, Ricci tensor, scalar curvature, Einstein tensor — together with the general
static spherically symmetric chart
`ds² = −f(r) dt² + f(r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`
carrying an arbitrary lapse `f`. Part II states that the two standard forms of the vacuum
equations agree away from dimension two. Parts III–XI state the solutions:

| part | solution | what is stated |
|---|---|---|
| III | **Schwarzschild** `f = 1 − 2M/r` | `R_{μν} = 0`, `G_{μν} = 0`, `R = 0` |
| IV | **Schwarzschild–de Sitter (Kottler)** `f = 1 − 2M/r − Λr²/3` | `R_{μν} = Λ g_{μν}` |
| V | areal static gauge | the Schwarzschild family is the **only** vacuum lapse |
| VI | **Reissner–Nordström** `f = 1 − 2M/r + Q²/r²` | `G_{μν} = 8π T_{μν}` for the *defined* Maxwell stress tensor of the Coulomb field — the full Einstein–Maxwell system — plus `R = 0` and `R_θθ = Q²/r² ≠ 0` |
| VII | **ingoing Vaidya** `ds² = −(1 − 2m(v)/r) dv² + 2 dv dr + r² dΩ²` | `R_{μν} = (2m′(v)/r²) δ^v_μ δ^v_ν`, rank-one null dust; `R = 0`; the Einstein-tensor form |
| VIII | **spatially flat FLRW** `ds² = −dt² + a(t)²(dx² + dy² + dz²)` | the two Friedmann equations in Einstein-tensor form, and vanishing off-diagonal `G` |
| IX | **static de Sitter** `f = 1 − r²/L²` | `R_{μν} = (3/L²) g_{μν}`, `R = 12/L²` |
| X | **Minkowski in spherical coordinates** `f = 1` | Ricci-flat — the sanity check |
| XI | **Kiselev** `f = 1 − 2M/r − c r^{−(3w+1)}` | `R_θθ = −3wc r^{−(3w+1)}`, nonzero for `w ≠ 0`; Ricci-flat at `w = 0` |

Parts VI–VIII are the *sourced* solutions: the field equations there are not `R_{μν} = 0` but
an identity relating curvature to a source term. Parts III–V and IX–XI are vacuum or
Λ-vacuum. Exactly what "vacuum" and "sourced" mean in each case is spelled out below.

## Mathlib has no curvature, so the whole chain is defined here

Grepped case-insensitively across all 8,264 `.lean` files of Mathlib at revision
`81a5d257c8e410db227a6665ed08f64fea08e997` (tag `v4.32.0`), checked for this entry:
`christoffel`, `leviCivita`, `levi_civita`, `riemannCurvature`, `curvatureTensor`, `ricci`,
`scalarCurvature`, `sectionalCurvature`, `Lorentzian` and `PseudoRiemannian` each return **zero
hits**. The one metric structure Mathlib does have,
`Mathlib/Topology/VectorBundle/Riemannian.lean`'s `RiemannianMetric`, carries literal
positive-definiteness in its `pos` field and therefore cannot express signature `(−,+,+,+)`.

Every definition below is consequently given here from Mathlib primitives only — `deriv`,
`Function.update`, `Finset.sum`, `Matrix.diagonal`, `Matrix.inv`, `Real.sin` — with no
structures, no typeclasses and no `Prop`-valued bundling. Each carries its ordinary
mathematical meaning and is used with no other.

## Conventions, stated explicitly

* `∂_b F` is `pderiv b F`: the derivative of `F` along the `b`-th coordinate line.
* `Γ^a_{bc} = ½ gᵃᵈ (∂_b g_{dc} + ∂_c g_{db} − ∂_d g_{bc})` — Wald (3.1.30), MTW (8.24),
  Carroll (3.27). Upper index first, lower index pair `(b, c)`, sum over `d` across `Fin n`.
* `R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} − Γ^a_{de} Γ^e_{cb}` — Wald
  (3.2.3), Carroll (3.66). This is the convention in which the round sphere and de Sitter space
  have *positive* scalar curvature. The opposite overall sign is also current in the literature
  and is **not** the one used here.
* `R_{bd} = R^a_{bad}` — the Ricci tensor is the contraction on the **first and third** slots.
* `R = gᵇᵈ R_{bd}` and `G_{bd} = R_{bd} − ½ R g_{bd}`.
* `gᵃᵈ` is Mathlib's `Matrix.inv` applied to `g x`. That is the true inverse exactly when the
  determinant is a unit, and its junk value at a singular matrix is `0`; every statement below
  is made either under an explicit `IsUnit (g x).det` hypothesis or on a region where
  nondegeneracy of the chart is part of the hypotheses.

## What is NOT claimed — read this before the statements

* **Nothing here is a manifold-level statement.** There is no atlas, no manifold, no vector
  bundle, no coordinate-independence theorem, and no claim that the objects defined here
  transform tensorially. Every statement is a computation in one fixed chart.
* **No global or maximal extension.** The Schwarzschild chart used here is the exterior region
  only. The horizon `r = 2M`, the interior `r < 2M`, the singularity `r = 0`, the coordinate
  poles `sin θ = 0`, and every maximal extension (Kruskal–Szekeres and the rest) lie outside
  every statement below, and nothing is claimed about them. Likewise for the Schwarzschild–de
  Sitter horizons.
* **No uniqueness beyond the stated gauge.** Part V is *not* Birkhoff's theorem. Staticity,
  spherical symmetry, the areal radial coordinate and the reciprocal lapse/radial-metric pair
  are all *assumed* there, whereas the genuine Birkhoff theorem derives staticity from the
  vacuum equations for a general, possibly time-dependent, spherically symmetric metric. What
  is compared is the calculus core of the classical argument once that gauge is fixed.
* **No symmetry of the Ricci tensor in general, and no Bianchi identities.** `R_{bd} = R_{db}`
  reduces to Clairaut's theorem for `pderiv`, which Mathlib supplies only for `fderiv`. The
  supporting library does **not** prove it in general, no symmetry lemma is compared, and no
  compared proof uses one. In the solutions below symmetry is *exhibited* rather than invoked:
  all sixteen components are computed and the off-diagonal ones shown to vanish identically for
  an arbitrary lapse. The Bianchi identities are absent for the same reason.
* **"Vacuum" and "sourced" mean exactly what the statements say, per solution.** For Parts III,
  V, X and the `w = 0` case of XI, "vacuum" means exactly `R_{μν} = 0` (equivalently
  `G_{μν} = 0`) as an identity between real numbers at each point of the stated region. For
  Parts IV and IX it means exactly `R_{μν} = Λ g_{μν}`. For Part VI a stress-energy tensor **is**
  defined — the Maxwell tensor `T_{μν} = (1/4π)(F_{μα}F_ν{}^α − ¼ g_{μν}F_{αβ}F^{αβ})` of the
  Coulomb field `F = (Q/r²) dt ∧ dr` — and `G_{μν} = 8π T_{μν}` is proved for it; that is the
  Einstein half of the Einstein–Maxwell system, and Maxwell's equations `∇_μ F^{μν} = 0` and
  `dF = 0` are **not** stated or used. For Parts VII and VIII **no** stress-energy tensor is
  defined at all: the statements compute `R_{μν}` and `G_{μν}` and exhibit their form, and
  calling the Vaidya source "null dust" or the FLRW source "a perfect fluid" is a description
  of that form, not a formalized claim about matter. No energy condition appears anywhere.
* **Vaidya is the INGOING chart, with the sign fixed.** Part VII uses ingoing
  Eddington–Finkelstein coordinates `(v, r, θ, φ)` with `g_{vr} = g_{rv} = +1`, i.e.
  `ds² = −(1 − 2m(v)/r) dv² + 2 dv dr + r² dΩ²`. The outgoing chart (`−2 du dr`) is a different
  metric and is not treated. `m` is required only to be **once** differentiable near `v`; no
  second derivative of `m` is requested by any compared statement, which is deliberate.
* **FLRW is spatially FLAT only.** Part VIII is `k = 0` in Cartesian comoving coordinates.
  The open and closed FLRW charts are not treated, and nothing is claimed about them.
* **Kiselev's exponent is a real power.** Part XI uses `Real.rpow` for `r^{−(3w+1)}` and is
  stated on `r > 0` only. No claim is made that quintessence with that equation of state is
  physical, and no matter model is formalized.
* **No numerical or asymptotic content.** Every statement is an exact pointwise identity.

Conventions follow the standard textbooks — Wald, *General Relativity* (1984); Misner, Thorne
and Wheeler, *Gravitation* (1973); Carroll, *Spacetime and Geometry* (2019) — cited for the
conventions only. Part III's metric is Schwarzschild's (Sitzungsber. Preuss. Akad. Wiss. Berlin,
1916, 189–196), Part IV's is Kottler's (Ann. Phys. **361** (1918), 401–462), and Part V's
statement is Jebsen's (1921) and Birkhoff's (*Relativity and Modern Physics*, 1923).
-/

namespace SchwarzschildVacuum

open Matrix Filter Topology

variable {n : ℕ}

/-! # Part I — the definitional chain

Shared by every solution below. Nothing in this part is specific to any one metric.
-/

/-! ## I.1 The coordinate partial derivative -/

/-- The coordinate line through `x` in the `b`-th direction: the point `x` with its `b`-th
coordinate replaced by `t`, every other coordinate frozen. -/
noncomputable def coordLine (x : Fin n → ℝ) (b : Fin n) (t : ℝ) : Fin n → ℝ :=
  Function.update x b t

/-- **The coordinate partial derivative** `∂F/∂x^b` at `x`, realised as the one-variable
derivative of `F` restricted to the `b`-th coordinate line through `x`. This is literally the
textbook partial derivative. It is total: where the section is not differentiable it returns
Mathlib's `deriv` junk value `0`, exactly as `deriv` itself does. -/
noncomputable def pderiv (b : Fin n) (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t : ℝ => F (coordLine x b t)) (x b)

/-! ## I.2 Chart-level curvature -/

/-- A chart-level metric: a matrix-valued function on (an open subset of) `ℝⁿ`. No positivity,
symmetry or invertibility is assumed by the type, which is what allows Lorentzian signature. -/
abbrev MetricFn (n : ℕ) := (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ

/-- Pointwise symmetry of a chart-level metric, `g_{ij} = g_{ji}` at every point. -/
def IsSymmetricMetric (g : MetricFn n) : Prop := ∀ y i j, g y i j = g y j i

/-- **Christoffel symbols of the second kind**,
`Γ^a_{bc} = ½ gᵃᵈ (∂_b g_{dc} + ∂_c g_{db} − ∂_d g_{bc})`
(Wald (3.1.30), MTW (8.24), Carroll (3.27)), with `gᵃᵈ = (g x)⁻¹ a d` Mathlib's matrix
inverse. -/
noncomputable def christoffel (g : MetricFn n) (x : Fin n → ℝ) (a b c : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin n, (g x)⁻¹ a d *
    (pderiv b (fun y => g y d c) x + pderiv c (fun y => g y d b) x
      - pderiv d (fun y => g y b c) x)

/-- **Riemann curvature tensor**, `(1,3)` form,
`R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} − Γ^a_{de} Γ^e_{cb}`
(Wald (3.2.3), Carroll (3.66)) — the sign convention in which de Sitter space has positive
scalar curvature. -/
noncomputable def riemann (g : MetricFn n) (x : Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  pderiv c (fun y => christoffel g y a d b) x - pderiv d (fun y => christoffel g y a c b) x
    + ∑ e : Fin n, (christoffel g x a c e * christoffel g x e d b
        - christoffel g x a d e * christoffel g x e c b)

/-- **Ricci tensor**, `R_{bd} = R^a_{bad}`: the contraction of the Riemann tensor on its first
and third slots. -/
noncomputable def ricci (g : MetricFn n) (x : Fin n → ℝ) (b d : Fin n) : ℝ :=
  ∑ a : Fin n, riemann g x a b a d

/-- **Scalar curvature**, `R = gᵇᵈ R_{bd}`. -/
noncomputable def scalarCurvature (g : MetricFn n) (x : Fin n → ℝ) : ℝ :=
  ∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * ricci g x b d

/-- **Einstein tensor**, `G_{bd} = R_{bd} − ½ R g_{bd}`. -/
noncomputable def einstein (g : MetricFn n) (x : Fin n → ℝ) (b d : Fin n) : ℝ :=
  ricci g x b d - (1 / 2 : ℝ) * scalarCurvature g x * g x b d

/-- A chart-level metric is **Ricci-flat at `x`** — i.e. solves the vacuum Einstein equation
there — when every component of its Ricci tensor vanishes at `x`. -/
def RicciFlatAt (g : MetricFn n) (x : Fin n → ℝ) : Prop := ∀ b d, ricci g x b d = 0

/-! ## I.3 The static spherically symmetric chart -/

/-- The general static spherically symmetric metric with lapse `f`, in areal-radius gauge:
`diag(−f(r), 1/f(r), r², r² sin²θ)` in coordinates `(t, r, θ, φ)`, i.e.
`ds² = −f(r) dt² + f(r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`. -/
noncomputable def ssMetric (f : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.diagonal ![-(f (x 1)), (f (x 1))⁻¹, (x 1) ^ 2, (x 1) ^ 2 * Real.sin (x 2) ^ 2]

/-! # Part II — the two forms of the vacuum equations -/

/-- **The vacuum field equations in the two standard forms are equivalent away from dimension
two.** For a symmetric chart-level metric whose determinant is invertible at `x`, and for
`n ≠ 2`, the Einstein tensor vanishes at `x` in every component if and only if the Ricci tensor
does. This is the general fact that licenses using "Ricci-flat" and "solves the vacuum
equations" interchangeably; it is proved rather than assumed. `n = 2` is genuinely excluded:
there the Einstein tensor vanishes identically for every metric, so the two conditions come
apart. -/
theorem einstein_eq_zero_iff_ricciFlat {g : MetricFn n} (hg : IsSymmetricMetric g)
    {x : Fin n → ℝ} (hx : IsUnit (g x).det) (hn : (n : ℝ) ≠ 2) :
    (∀ b d, einstein g x b d = 0) ↔ RicciFlatAt g x := by
  sorry

/-! # Part III — Schwarzschild

`ds² = −(1 − 2M/r) dt² + (1 − 2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`.
-/

/-- The Schwarzschild lapse `f(r) = 1 − 2M/r`, with `G = c = 1`. -/
noncomputable def schwF (M : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s

/-- **The Schwarzschild metric** of mass `M` in Schwarzschild coordinates:
`diag(−(1 − 2M/r), (1 − 2M/r)⁻¹, r², r² sin²θ)`. -/
noncomputable def schwarzschild (M : ℝ) : MetricFn 4 := ssMetric (schwF M)

/-- The **Schwarzschild exterior chart**: the open region `r > 0`, `r > 2M`, `sin θ ≠ 0` of
`ℝ⁴`. The horizon, the interior, the singularity and the coordinate poles are excluded — the
chart degenerates at each of them. -/
def SchwExterior (M : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ 2 * M < x 1 ∧ Real.sin (x 2) ≠ 0}

/-- **The Schwarzschild metric solves the vacuum Einstein equations.**

At every point of the exterior chart `r > 2M > 0`, `sin θ ≠ 0`, every one of the sixteen
components of the Ricci tensor of `diag(−(1 − 2M/r), (1 − 2M/r)⁻¹, r², r² sin²θ)` is zero.

Scope: this is a statement about that one chart. It says nothing at `r = 2M`, at `r ≤ 0`, at
`sin θ = 0`, or about any extension of the chart. -/
theorem schwarzschild_ricciFlat {M : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ SchwExterior M) :
    RicciFlatAt (schwarzschild M) x := by
  sorry

/-- **The Einstein tensor of Schwarzschild vanishes**, `G_{μν} = 0`, on the same exterior
chart — the field equations in the form in which they are usually written. -/
theorem schwarzschild_einstein_eq_zero {M : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ SchwExterior M)
    (b d : Fin 4) : einstein (schwarzschild M) x b d = 0 := by
  sorry

/-- **The scalar curvature of Schwarzschild vanishes** on the exterior chart. Note that this is
*not* a flatness statement: the Kretschmann scalar of Schwarzschild is `48M²/r⁶ ≠ 0`, which is
not formalized here. -/
theorem schwarzschild_scalarCurvature_eq_zero {M : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ SchwExterior M) : scalarCurvature (schwarzschild M) x = 0 := by
  sorry

/-! # Part IV — Schwarzschild–de Sitter (Kottler)

`ds² = −f dt² + f⁻¹ dr² + r² dΩ²` with `f = 1 − 2M/r − Λr²/3`.
-/

/-- The Schwarzschild–de Sitter lapse `f(r) = 1 − 2M/r − Λr²/3` (Kottler 1918). -/
noncomputable def sdsF (M Λ : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s - Λ * s ^ 2 / 3

/-- **Schwarzschild–de Sitter is an Einstein space**, `R_{μν} = Λ g_{μν}`: the static
spherically symmetric metric with lapse `f = 1 − 2M/r − Λr²/3` solves the vacuum Einstein
equations with cosmological constant `Λ`.

The hypotheses are the nondegeneracy of the chart at `x` (`r ≠ 0`, `sin θ ≠ 0`) together with
`f ≠ 0` and `r ≠ 0` on a *neighbourhood* of `r`, which is what differentiating the metric
requires; `∀ᶠ s in 𝓝 (x 1), P s` is Mathlib's "`P` holds near `x 1`".

Besides being the Λ-vacuum solution used throughout the junction-condition literature, this
statement pins the sign of the curvature convention: with the conventions fixed above, positive
`Λ` gives positive curvature. It also certifies that `ricci` is not accidentally identically
zero — at `Λ ≠ 0` the `θθ` component is `Λr² ≠ 0`. -/
theorem ricci_sds {M Λ : ℝ} {x : Fin 4 → ℝ} (hr : x 1 ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (hF : ∀ᶠ s in 𝓝 (x 1), sdsF M Λ s ≠ 0) (hR : ∀ᶠ s in 𝓝 (x 1), s ≠ 0) (b d : Fin 4) :
    ricci (ssMetric (sdsF M Λ)) x b d = Λ * ssMetric (sdsF M Λ) x b d := by
  sorry

/-! # Part V — uniqueness in the areal static spherically symmetric gauge -/

/-- **Uniqueness of the Schwarzschild lapse in the areal-radius static spherically symmetric
gauge** — the calculus core of Birkhoff's theorem in that gauge.

For the chart `ds² = −f dt² + f⁻¹ dr² + r² dΩ²` the `θθ` Ricci component is `1 − f − r f′`, so
the single vacuum equation `R_θθ = 0` is the first-order linear ODE `r f′ + f − 1 = 0`. The
statement below is exactly that ODE, in Mathlib vocabulary and with no definition of its own:
on an interval `(a, b)` avoiding `r = 0`, every `f` with derivative `f₁` satisfying
`1 − f − r f₁ = 0` throughout is `f = 1 − 2M/r` for a single constant `M`.

**This is not Birkhoff's theorem.** Staticity, spherical symmetry, the areal radial coordinate
and the reciprocal lapse pair are assumed here; the genuine theorem derives staticity from the
vacuum equations for a general spherically symmetric metric. The link between `R_θθ` and this
ODE is proved elsewhere in the supporting library and is not part of this statement. -/
theorem exists_mass_of_areal_vacuum {f f₁ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ r ∈ Set.Ioo a b, HasDerivAt f (f₁ r) r)
    (hz : ∀ r ∈ Set.Ioo a b, 1 - f r - r * f₁ r = 0)
    (h0 : ∀ r ∈ Set.Ioo a b, r ≠ 0) :
    ∃ M : ℝ, ∀ r ∈ Set.Ioo a b, f r = 1 - 2 * M / r := by
  sorry

/-! # Part VI — Reissner–Nordström, and the Einstein–Maxwell system

`ds² = −f dt² + f⁻¹ dr² + r² dΩ²` with `f = 1 − 2M/r + Q²/r²`, sourced by the Coulomb field
`F = (Q/r²) dt ∧ dr`.  This is the one place in this file where a stress-energy tensor is
defined, and where the field equations are therefore an identity between curvature and a
source rather than a vanishing statement.
-/

/-- The Reissner–Nordström lapse `f(r) = 1 − 2M/r + Q²/r²`. -/
noncomputable def rnF (M Q : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s + Q ^ 2 / s ^ 2

/-- **The Reissner–Nordström metric** of mass `M` and charge `Q`. -/
noncomputable def reissnerNordstrom (M Q : ℝ) : MetricFn 4 := ssMetric (rnF M Q)

/-- The region where the chart is a chart: `r > 0`, off both horizons (`f ≠ 0`), off the
coordinate poles. -/
def RNRegion (M Q : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ rnF M Q (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}

/-- **Faraday tensor of the Coulomb field**, `F = (Q/r²) dt ∧ dr`, as the antisymmetric matrix
with `F_{tr} = Q/r² = −F_{rt}` and every other entry zero.  This is the radial electric field
of a point charge `Q` in these coordinates. -/
noncomputable def coulombF (Q : ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, Q / (x 1) ^ 2, 0, 0], ![-(Q / (x 1) ^ 2), 0, 0, 0],
              ![0, 0, 0, 0], ![0, 0, 0, 0]]

/-- `F^{μν} = g^{μα} g^{νβ} F_{αβ}` — both indices raised with the inverse metric. -/
noncomputable def faradayUp (g : MetricFn 4) (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, (g x)⁻¹ μ α * (g x)⁻¹ ν β * F x α β

/-- The electromagnetic invariant `F_{αβ} F^{αβ}` (equal to `2(B² − E²)` in flat space). -/
noncomputable def faradayInvariant (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, F x α β * faradayUp g F x α β

/-- `F_{μα} F_ν{}^α = F_{μα} g^{αβ} F_{νβ}` — one index raised, then contracted. -/
noncomputable def faradayContract (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, F x μ α * (g x)⁻¹ α β * F x ν β

/-- **The Maxwell stress-energy tensor**
`T_{μν} = (1/4π)(F_{μα} F_ν{}^α − ¼ g_{μν} F_{αβ} F^{αβ})`
— MTW (5.6), Wald (6.5.4), in Gaussian units with `G = c = 1`.  This is the only
stress-energy tensor defined anywhere in this file. -/
noncomputable def stressEM (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  (1 / (4 * Real.pi)) * (faradayContract g F x μ ν
    - (1 / 4 : ℝ) * g x μ ν * faradayInvariant g F x)

/-- **Reissner–Nordström is not Ricci-flat**: the `θθ` component of its Ricci tensor is
`Q²/r²`, nonzero whenever the charge is.  Stated because it is the falsifier for Part III —
a charged black hole is *not* a vacuum, and the framework has to see the difference. -/
theorem ricci_rn_thetaTheta {M Q : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ RNRegion M Q) :
    ricci (reissnerNordstrom M Q) x 2 2 = Q ^ 2 / (x 1) ^ 2 := by
  sorry

/-- **Reissner–Nordström has vanishing scalar curvature.**  This is the tracelessness of the
electromagnetic stress tensor in four dimensions, read off the geometry. -/
theorem reissnerNordstrom_scalarCurvature_eq_zero {M Q : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ RNRegion M Q) : scalarCurvature (reissnerNordstrom M Q) x = 0 := by
  sorry

/-- **The electromagnetic invariant of the Coulomb field**, `F_{αβ} F^{αβ} = −2Q²/r⁴`.
Negative, as it must be for a purely electric field. -/
theorem faradayInvariant_coulomb {M Q : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ RNRegion M Q) :
    faradayInvariant (reissnerNordstrom M Q) (coulombF Q) x = -(2 * Q ^ 2 / (x 1) ^ 4) := by
  sorry

/-- **The Einstein–Maxwell equations for the charged black hole**:
`G_{μν} = 8π T_{μν}`, in all sixteen components, on the whole chart region, where `T` is the
Maxwell stress-energy tensor of the Coulomb field defined above and every index is raised with
the inverse Reissner–Nordström metric.

Both sides are built from the definitions in this file, so this is the Einstein half of the
Einstein–Maxwell system stated in full.  **Maxwell's own equations are not part of it**:
neither `∇_μ F^{μν} = 0` nor `dF = 0` is stated or used anywhere. -/
theorem reissnerNordstrom_einstein_eq_maxwell {M Q : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ RNRegion M Q) (b d : Fin 4) :
    einstein (reissnerNordstrom M Q) x b d
      = 8 * Real.pi * stressEM (reissnerNordstrom M Q) (coulombF Q) x b d := by
  sorry

/-! # Part VII — ingoing Vaidya: a non-static, non-diagonal chart

`ds² = −(1 − 2m(v)/r) dv² + 2 dv dr + r² dΩ²` in ingoing Eddington–Finkelstein coordinates
`(v, r, θ, φ) = (x 0, x 1, x 2, x 3)`, with `g_{vr} = g_{rv} = +1`.  The mass function `m` is
arbitrary and is required only to be **once** differentiable near `v`.
-/

/-- **The ingoing Vaidya metric**, as the matrix
`[[−(1 − 2m(v)/r), 1, 0, 0], [1, 0, 0, 0], [0, 0, r², 0], [0, 0, 0, r² sin²θ]]`
in coordinates `(v, r, θ, φ)`.  Unlike every other metric in this file it is neither static
nor diagonal, and its inverse has `g^{vv} = 0`. -/
noncomputable def vaidyaMetric (m : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.of ![![-(1 - 2 * m (x 0) / x 1), 1, 0, 0],
              ![1, 0, 0, 0],
              ![0, 0, (x 1) ^ 2, 0],
              ![0, 0, 0, (x 1) ^ 2 * Real.sin (x 2) ^ 2]]

/-- The Ricci tensor of the ingoing Vaidya metric written as a table indexed `[b][d]`: rank one
and null, with the single nonzero entry `R_{vv} = 2 m′(v)/r²`. -/
noncomputable def vRicci (m₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![2 * m₁ (x 0) / (x 1) ^ 2, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

/-- **The Vaidya Ricci tensor is rank-one null dust**:
`R_{μν} = (2 m′(v)/r²) δ^v_μ δ^v_ν`, for an arbitrary once-differentiable mass function.

The hypothesis is `HasDerivAt m (m₁ s) s` near `v` — first derivative only.  No second
derivative of `m` is requested, which matters: the physically interesting Vaidya gluings have
`m` of class `C¹` but not `C²`, and a statement needing `m″` would exclude them. -/
theorem ricci_vaidya_null_dust {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt m (m₁ s) s)
    (hR : ∀ᶠ s in 𝓝 (x 1), s ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) (b d : Fin 4) :
    ricci (vaidyaMetric m) x b d
      = 2 * m₁ (x 0) / (x 1) ^ 2 * (if b = 0 then (1 : ℝ) else 0)
          * (if d = 0 then (1 : ℝ) else 0) := by
  sorry

/-- **Vaidya has vanishing scalar curvature.**  Not a cancellation: the only nonvanishing Ricci
component is `R_{vv}` and the ingoing inverse metric has `g^{vv} = 0`, so the trace vanishes
because the Ricci tensor is null — the same mechanism that makes null dust traceless. -/
theorem vaidya_scalarCurvature_eq_zero {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt m (m₁ s) s)
    (hR : ∀ᶠ s in 𝓝 (x 1), s ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) : scalarCurvature (vaidyaMetric m) x = 0 := by
  sorry

/-- **The Einstein tensor of Vaidya equals its Ricci tensor**, since `R = 0`; so
`G_{μν} = (2 m′(v)/r²) δ^v_μ δ^v_ν`, the Einstein-tensor form of the null-dust statement. -/
theorem einstein_vaidya {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt m (m₁ s) s)
    (hR : ∀ᶠ s in 𝓝 (x 1), s ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) (b d : Fin 4) :
    einstein (vaidyaMetric m) x b d = vRicci m₁ x b d := by
  sorry

/-! # Part VIII — spatially flat FLRW, and the Friedmann equations

`ds² = −dt² + a(t)²(dx² + dy² + dz²)` in Cartesian comoving coordinates
`(t, x, y, z) = (x 0, x 1, x 2, x 3)`.  Spatially flat only: `k = 0`.
-/

/-- **Spatially flat FLRW** in Cartesian comoving coordinates, scale factor `a(t)`. -/
noncomputable def flrwMetric (a : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.diagonal ![-1, (a (x 0)) ^ 2, (a (x 0)) ^ 2, (a (x 0)) ^ 2]

/-- **The first Friedmann equation, in Einstein-tensor form**: `G_tt = 3(ȧ/a)²`.

Coupled to a perfect fluid through `G_{μν} = 8π T_{μν}` this is `H² = 8πρ/3` — but no fluid is
defined here and that coupling is not part of the statement.  What is stated is the value of
one component of the Einstein tensor of the metric above. -/
theorem friedmann_first {a a₁ a₂ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt a (a₁ s) s)
    (hA : ∀ᶠ s in 𝓝 (x 0), a s ≠ 0)
    (hd2 : HasDerivAt a₁ (a₂ (x 0)) (x 0)) :
    einstein (flrwMetric a) x 0 0 = 3 * (a₁ (x 0) / a (x 0)) ^ 2 := by
  sorry

/-- **The second Friedmann equation, in Einstein-tensor form**: `G_ii = −(2 a ä + ȧ²)` for each
of the three spatial directions.  Again no fluid is defined; the acceleration equation follows
only once one is. -/
theorem friedmann_second {a a₁ a₂ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt a (a₁ s) s)
    (hA : ∀ᶠ s in 𝓝 (x 0), a s ≠ 0)
    (hd2 : HasDerivAt a₁ (a₂ (x 0)) (x 0)) (i : Fin 4) (hi : i ≠ 0) :
    einstein (flrwMetric a) x i i = -(2 * a (x 0) * a₂ (x 0) + a₁ (x 0) ^ 2) := by
  sorry

/-- **Every off-diagonal component of the FLRW Einstein tensor vanishes** — no momentum flux and
no anisotropic stress, which is what makes the two equations above the whole content. -/
theorem einstein_flrw_offDiag {a a₁ a₂ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt a (a₁ s) s)
    (hA : ∀ᶠ s in 𝓝 (x 0), a s ≠ 0)
    (hd2 : HasDerivAt a₁ (a₂ (x 0)) (x 0)) (b d : Fin 4) (h : b ≠ d) :
    einstein (flrwMetric a) x b d = 0 := by
  sorry

/-! # Part IX — static de Sitter

`ds² = −f dt² + f⁻¹ dr² + r² dΩ²` with `f = 1 − r²/L²`: the static patch, `Λ = 3/L²`.
-/

/-- The static de Sitter lapse `f(r) = 1 − r²/L²`, with Hubble length `L`. -/
noncomputable def dsF (L : ℝ) : ℝ → ℝ := fun s => 1 - s ^ 2 / L ^ 2

/-- **The static de Sitter metric** with Hubble length `L`. -/
noncomputable def deSitterStatic (L : ℝ) : MetricFn 4 := ssMetric (dsF L)

/-- The region on which the static-patch chart is a chart: `r > 0`, off the cosmological
horizon `r = L`, off the coordinate poles. -/
def DSRegion (L : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ dsF L (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}

/-- **Static de Sitter is an Einstein space**, `R_{μν} = (3/L²) g_{μν}`: it solves the vacuum
equations with cosmological constant `Λ = 3/L²`.  With Part IV this is the second
nonvanishing-curvature control on the sign of the convention. -/
theorem ricci_deSitterStatic {L : ℝ} {x : Fin 4 → ℝ} (hL : L ≠ 0) (hx : x ∈ DSRegion L)
    (b d : Fin 4) :
    ricci (deSitterStatic L) x b d = (3 / L ^ 2) * deSitterStatic L x b d := by
  sorry

/-- **The scalar curvature of static de Sitter is `12/L²`** — constant, as it must be for a
maximally symmetric space, and positive, which is de Sitter rather than anti-de Sitter.  In the
opposite sign convention this number would be negative; it is the sharpest single check that
the convention fixed in this file is the one advertised. -/
theorem deSitterStatic_scalarCurvature {L : ℝ} {x : Fin 4 → ℝ} (hL : L ≠ 0)
    (hx : x ∈ DSRegion L) : scalarCurvature (deSitterStatic L) x = 12 / L ^ 2 := by
  sorry

/-! # Part X — Minkowski in spherical coordinates: the sanity check -/

/-- The constant lapse `f = 1`. -/
noncomputable def flatF : ℝ → ℝ := fun _ => 1

/-- **Minkowski space in spherical coordinates**,
`ds² = −dt² + dr² + r² dθ² + r² sin²θ dφ²`. -/
noncomputable def minkowskiSpherical : MetricFn 4 := ssMetric flatF

/-- **Minkowski space in spherical coordinates is Ricci-flat.**

The point of stating something this elementary is that the areal-radius chart of *flat* space
still has nine nonvanishing entries in its 64-entry Christoffel table — six distinct symbols
up to the symmetry of the lower indices (`Γ^r_{θθ} = −r`, `Γ^r_{φφ} = −r sin²θ`,
`Γ^θ_{rθ} = 1/r`, `Γ^θ_{φφ} = −sin θ cos θ`, `Γ^φ_{rφ} = 1/r`, `Γ^φ_{θφ} = cot θ`).  So the Riemann and Ricci tensors returning zero here is a statement
about cancellation among nonzero connection coefficients, not about a trivially empty table —
which is exactly the failure mode a curvature definition could have and still prove every
vacuum theorem in this file. -/
theorem minkowskiSpherical_ricciFlat {x : Fin 4 → ℝ} (hr : x 1 ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) : RicciFlatAt minkowskiSpherical x := by
  sorry

/-! # Part XI — Kiselev: a real-power radial profile

`f = 1 − 2M/r − c r^{−(3w+1)}`, the quintessence-surrounded black hole.  The exponent is a real
number, so the power is `Real.rpow` and the chart is stated on `r > 0` only.
-/

/-- The Kiselev lapse `f(r) = 1 − 2M/r − c r^{−(3w+1)}`, with `w` the equation-of-state
parameter of the surrounding fluid.  The exponent is real, so the power is `Real.rpow`. -/
noncomputable def kiselevF (M c w : ℝ) : ℝ → ℝ :=
  fun s => 1 - 2 * M / s - c * s ^ (-(3 * w + 1))

/-- **The Kiselev metric**: a black hole surrounded by quintessence of equation of state `w`. -/
noncomputable def kiselev (M c w : ℝ) : MetricFn 4 := ssMetric (kiselevF M c w)

/-- **The `θθ` Ricci component of the Kiselev metric is `−3wc r^{−(3w+1)}`.**

Nonzero whenever `w ≠ 0` and `c ≠ 0`: the quintessence really does curve the metric, and the
definitions in Part I see it.  Two degenerations are worth naming, and neither is claimed as a
compared theorem: at `w = 1/3` the lapse is Reissner–Nordström with `Q² = −c` (note the sign),
and at `w = −1` it is Schwarzschild–de Sitter with `Λ = 3c`. -/
theorem ricci_kiselev_thetaTheta {M c w : ℝ} {x : Fin 4 → ℝ} (hr : 0 < x 1)
    (hs : Real.sin (x 2) ≠ 0)
    (hF : ∀ᶠ s in 𝓝 (x 1), kiselevF M c w s ≠ 0) :
    ricci (kiselev M c w) x 2 2 = -(3 * w * c * (x 1) ^ (-(3 * w + 1))) := by
  sorry

/-- **Kiselev with `w = 0` is Ricci-flat.**  The dust case: `f = 1 − 2M/r − c/r` is
Schwarzschild with mass `M + c/2`, so the `c/r` term is a pure mass shift and carries no
curvature of its own. -/
theorem kiselev_ricciFlat_of_w_eq_zero {M c : ℝ} {x : Fin 4 → ℝ} (hr : 0 < x 1)
    (hs : Real.sin (x 2) ≠ 0)
    (hF : ∀ᶠ s in 𝓝 (x 1), kiselevF M c 0 s ≠ 0) :
    RicciFlatAt (kiselev M c 0) x := by
  sorry


end SchwarzschildVacuum
