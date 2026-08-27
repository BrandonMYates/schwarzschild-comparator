/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GRLab

/-!
# Solution

The proof development lives in the `GRLab` library, pinned by commit in `lakefile.toml`. This
file restates the Challenge's thirty-three definitions and twenty-one theorems verbatim and
discharges each theorem by direct application of the corresponding library theorem.

The thirty-three `example`s below are the bridge: each Challenge definition is *definitionally*
equal to its `GRLab` counterpart, checked by `rfl` at the level of the fully applied constant
(`@`-form, so the implicit `{n : ℕ}` is compared too). No translation step is involved anywhere.

Those bridges are the substance of this file, not boilerplate. The compared statements are
classical and no new mathematics is claimed by this entry; what it certifies is that `GRLab`'s
coordinate-level definitions — `pderiv`, `christoffel`, `riemann`, `ricci`, `scalarCurvature`,
`einstein`, and the Maxwell sector, in the sign and index conventions fixed in the Challenge —
reproduce the textbook answers on the standard exact solutions, vacuum and sourced alike, so
that later statements in the same programme can be made against the same definitions and read
with the same confidence.

One scope limitation, stated here because a reader of the library will find it: `GRLab` does
**not** prove `R_{bd} = R_{db}` in general. That reduces to Clairaut's theorem for `pderiv`,
which Mathlib supplies only for `fderiv`, and transporting it was scoped out. No general
symmetry lemma is compared. For each compared metric symmetry is instead *exhibited*: all
sixteen Ricci components are computed and the off-diagonal ones shown to vanish identically.
-/

namespace SchwarzschildVacuum

open Matrix Filter Topology

variable {n : ℕ}

/-! ## Part I — the definitional chain -/

noncomputable def coordLine (x : Fin n → ℝ) (b : Fin n) (t : ℝ) : Fin n → ℝ :=
  Function.update x b t

noncomputable def pderiv (b : Fin n) (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t : ℝ => F (coordLine x b t)) (x b)

abbrev MetricFn (n : ℕ) := (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ

def IsSymmetricMetric (g : MetricFn n) : Prop := ∀ y i j, g y i j = g y j i

noncomputable def christoffel (g : MetricFn n) (x : Fin n → ℝ) (a b c : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin n, (g x)⁻¹ a d *
    (pderiv b (fun y => g y d c) x + pderiv c (fun y => g y d b) x
      - pderiv d (fun y => g y b c) x)

noncomputable def riemann (g : MetricFn n) (x : Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  pderiv c (fun y => christoffel g y a d b) x - pderiv d (fun y => christoffel g y a c b) x
    + ∑ e : Fin n, (christoffel g x a c e * christoffel g x e d b
        - christoffel g x a d e * christoffel g x e c b)

noncomputable def ricci (g : MetricFn n) (x : Fin n → ℝ) (b d : Fin n) : ℝ :=
  ∑ a : Fin n, riemann g x a b a d

noncomputable def scalarCurvature (g : MetricFn n) (x : Fin n → ℝ) : ℝ :=
  ∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * ricci g x b d

noncomputable def einstein (g : MetricFn n) (x : Fin n → ℝ) (b d : Fin n) : ℝ :=
  ricci g x b d - (1 / 2 : ℝ) * scalarCurvature g x * g x b d

def RicciFlatAt (g : MetricFn n) (x : Fin n → ℝ) : Prop := ∀ b d, ricci g x b d = 0

noncomputable def ssMetric (f : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.diagonal ![-(f (x 1)), (f (x 1))⁻¹, (x 1) ^ 2, (x 1) ^ 2 * Real.sin (x 2) ^ 2]

/-! ## Part III — Schwarzschild: definitions -/

noncomputable def schwF (M : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s

noncomputable def schwarzschild (M : ℝ) : MetricFn 4 := ssMetric (schwF M)

def SchwExterior (M : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ 2 * M < x 1 ∧ Real.sin (x 2) ≠ 0}

/-! ## Part IV — Schwarzschild–de Sitter: definitions -/

noncomputable def sdsF (M Λ : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s - Λ * s ^ 2 / 3

/-! ## Part VI — Reissner–Nordström and the Maxwell sector: definitions -/

noncomputable def rnF (M Q : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s + Q ^ 2 / s ^ 2

noncomputable def reissnerNordstrom (M Q : ℝ) : MetricFn 4 := ssMetric (rnF M Q)

def RNRegion (M Q : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ rnF M Q (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}

noncomputable def coulombF (Q : ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, Q / (x 1) ^ 2, 0, 0], ![-(Q / (x 1) ^ 2), 0, 0, 0],
              ![0, 0, 0, 0], ![0, 0, 0, 0]]

noncomputable def faradayUp (g : MetricFn 4) (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, (g x)⁻¹ μ α * (g x)⁻¹ ν β * F x α β

noncomputable def faradayInvariant (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, F x α β * faradayUp g F x α β

noncomputable def faradayContract (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, F x μ α * (g x)⁻¹ α β * F x ν β

noncomputable def stressEM (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  (1 / (4 * Real.pi)) * (faradayContract g F x μ ν
    - (1 / 4 : ℝ) * g x μ ν * faradayInvariant g F x)

/-! ## Part VII — ingoing Vaidya: definitions -/

noncomputable def vaidyaMetric (m : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.of ![![-(1 - 2 * m (x 0) / x 1), 1, 0, 0],
              ![1, 0, 0, 0],
              ![0, 0, (x 1) ^ 2, 0],
              ![0, 0, 0, (x 1) ^ 2 * Real.sin (x 2) ^ 2]]

noncomputable def vRicci (m₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![2 * m₁ (x 0) / (x 1) ^ 2, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

/-! ## Part VIII — spatially flat FLRW: definitions -/

noncomputable def flrwMetric (a : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.diagonal ![-1, (a (x 0)) ^ 2, (a (x 0)) ^ 2, (a (x 0)) ^ 2]

/-! ## Part IX — static de Sitter: definitions -/

noncomputable def dsF (L : ℝ) : ℝ → ℝ := fun s => 1 - s ^ 2 / L ^ 2

noncomputable def deSitterStatic (L : ℝ) : MetricFn 4 := ssMetric (dsF L)

def DSRegion (L : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ dsF L (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}

/-! ## Part X — Minkowski in spherical coordinates: definitions -/

noncomputable def flatF : ℝ → ℝ := fun _ => 1

noncomputable def minkowskiSpherical : MetricFn 4 := ssMetric flatF

/-! ## Part XI — Kiselev: definitions -/

noncomputable def kiselevF (M c w : ℝ) : ℝ → ℝ :=
  fun s => 1 - 2 * M / s - c * s ^ (-(3 * w + 1))

noncomputable def kiselev (M c w : ℝ) : MetricFn 4 := ssMetric (kiselevF M c w)

/-! ## Definitional bridges

Each is closed by `rfl`, which is the proof that the Challenge's definitions are not merely
analogous to the library's but definitionally identical to them. -/

example : @coordLine = @GRLab.coordLine := rfl
example : @pderiv = @GRLab.pderiv := rfl
example : @MetricFn = @GRLab.MetricFn := rfl
example : @IsSymmetricMetric = @GRLab.IsSymmetricMetric := rfl
example : @christoffel = @GRLab.christoffel := rfl
example : @riemann = @GRLab.riemann := rfl
example : @ricci = @GRLab.ricci := rfl
example : @scalarCurvature = @GRLab.scalarCurvature := rfl
example : @einstein = @GRLab.einstein := rfl
example : @RicciFlatAt = @GRLab.RicciFlatAt := rfl
example : @ssMetric = @GRLab.ssMetric := rfl
example : @schwF = @GRLab.schwF := rfl
example : @schwarzschild = @GRLab.schwarzschild := rfl
example : @SchwExterior = @GRLab.SchwExterior := rfl
example : @sdsF = @GRLab.sdsF := rfl
example : @rnF = @GRLab.rnF := rfl
example : @reissnerNordstrom = @GRLab.reissnerNordstrom := rfl
example : @RNRegion = @GRLab.RNRegion := rfl
example : @coulombF = @GRLab.coulombF := rfl
example : @faradayUp = @GRLab.faradayUp := rfl
example : @faradayInvariant = @GRLab.faradayInvariant := rfl
example : @faradayContract = @GRLab.faradayContract := rfl
example : @stressEM = @GRLab.stressEM := rfl
example : @vaidyaMetric = @GRLab.vaidyaMetric := rfl
example : @vRicci = @GRLab.vRicci := rfl
example : @flrwMetric = @GRLab.flrwMetric := rfl
example : @dsF = @GRLab.dsF := rfl
example : @deSitterStatic = @GRLab.deSitterStatic := rfl
example : @DSRegion = @GRLab.DSRegion := rfl
example : @flatF = @GRLab.flatF := rfl
example : @minkowskiSpherical = @GRLab.minkowskiSpherical := rfl
example : @kiselevF = @GRLab.kiselevF := rfl
example : @kiselev = @GRLab.kiselev := rfl

/-! ## Part II — the two forms of the vacuum equations -/

theorem einstein_eq_zero_iff_ricciFlat {g : MetricFn n} (hg : IsSymmetricMetric g)
    {x : Fin n → ℝ} (hx : IsUnit (g x).det) (hn : (n : ℝ) ≠ 2) :
    (∀ b d, einstein g x b d = 0) ↔ RicciFlatAt g x :=
  GRLab.einstein_eq_zero_iff_ricciFlat hg hx hn

/-! ## Part III — Schwarzschild: theorems -/

theorem schwarzschild_ricciFlat {M : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ SchwExterior M) :
    RicciFlatAt (schwarzschild M) x :=
  GRLab.schwarzschild_ricciFlat hx

theorem schwarzschild_einstein_eq_zero {M : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ SchwExterior M)
    (b d : Fin 4) : einstein (schwarzschild M) x b d = 0 :=
  GRLab.schwarzschild_einstein_eq_zero hx b d

theorem schwarzschild_scalarCurvature_eq_zero {M : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ SchwExterior M) : scalarCurvature (schwarzschild M) x = 0 :=
  GRLab.schwarzschild_scalarCurvature_eq_zero hx

/-! ## Part IV — Schwarzschild–de Sitter: theorem -/

theorem ricci_sds {M Λ : ℝ} {x : Fin 4 → ℝ} (hr : x 1 ≠ 0) (hs : Real.sin (x 2) ≠ 0)
    (hF : ∀ᶠ s in 𝓝 (x 1), sdsF M Λ s ≠ 0) (hR : ∀ᶠ s in 𝓝 (x 1), s ≠ 0) (b d : Fin 4) :
    ricci (ssMetric (sdsF M Λ)) x b d = Λ * ssMetric (sdsF M Λ) x b d :=
  GRLab.ricci_sds hr hs hF hR b d

/-! ## Part V — uniqueness in the areal static spherically symmetric gauge -/

theorem exists_mass_of_areal_vacuum {f f₁ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ r ∈ Set.Ioo a b, HasDerivAt f (f₁ r) r)
    (hz : ∀ r ∈ Set.Ioo a b, 1 - f r - r * f₁ r = 0)
    (h0 : ∀ r ∈ Set.Ioo a b, r ≠ 0) :
    ∃ M : ℝ, ∀ r ∈ Set.Ioo a b, f r = 1 - 2 * M / r :=
  GRLab.exists_mass_of_areal_vacuum hab hd hz h0

/-! ## Part VI — Reissner–Nordström: theorems -/

theorem ricci_rn_thetaTheta {M Q : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ RNRegion M Q) :
    ricci (reissnerNordstrom M Q) x 2 2 = Q ^ 2 / (x 1) ^ 2 :=
  GRLab.ricci_rn_thetaTheta hx

theorem reissnerNordstrom_scalarCurvature_eq_zero {M Q : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ RNRegion M Q) : scalarCurvature (reissnerNordstrom M Q) x = 0 :=
  GRLab.reissnerNordstrom_scalarCurvature_eq_zero hx

theorem faradayInvariant_coulomb {M Q : ℝ} {x : Fin 4 → ℝ} (hx : x ∈ RNRegion M Q) :
    faradayInvariant (reissnerNordstrom M Q) (coulombF Q) x = -(2 * Q ^ 2 / (x 1) ^ 4) :=
  GRLab.faradayInvariant_coulomb hx

theorem reissnerNordstrom_einstein_eq_maxwell {M Q : ℝ} {x : Fin 4 → ℝ}
    (hx : x ∈ RNRegion M Q) (b d : Fin 4) :
    einstein (reissnerNordstrom M Q) x b d
      = 8 * Real.pi * stressEM (reissnerNordstrom M Q) (coulombF Q) x b d :=
  GRLab.reissnerNordstrom_einstein_eq_maxwell hx b d

/-! ## Part VII — ingoing Vaidya: theorems -/

theorem ricci_vaidya_null_dust {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt m (m₁ s) s)
    (hR : ∀ᶠ s in 𝓝 (x 1), s ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) (b d : Fin 4) :
    ricci (vaidyaMetric m) x b d
      = 2 * m₁ (x 0) / (x 1) ^ 2 * (if b = 0 then (1 : ℝ) else 0)
          * (if d = 0 then (1 : ℝ) else 0) :=
  GRLab.ricci_vaidya_null_dust hD hR hs b d

theorem vaidya_scalarCurvature_eq_zero {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt m (m₁ s) s)
    (hR : ∀ᶠ s in 𝓝 (x 1), s ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) : scalarCurvature (vaidyaMetric m) x = 0 :=
  GRLab.vaidya_scalarCurvature_eq_zero hD hR hs

theorem einstein_vaidya {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt m (m₁ s) s)
    (hR : ∀ᶠ s in 𝓝 (x 1), s ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) (b d : Fin 4) :
    einstein (vaidyaMetric m) x b d = vRicci m₁ x b d :=
  GRLab.einstein_vaidya hD hR hs b d

/-! ## Part VIII — spatially flat FLRW: theorems -/

theorem friedmann_first {a a₁ a₂ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt a (a₁ s) s)
    (hA : ∀ᶠ s in 𝓝 (x 0), a s ≠ 0)
    (hd2 : HasDerivAt a₁ (a₂ (x 0)) (x 0)) :
    einstein (flrwMetric a) x 0 0 = 3 * (a₁ (x 0) / a (x 0)) ^ 2 :=
  GRLab.friedmann_first hD hA hd2

theorem friedmann_second {a a₁ a₂ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt a (a₁ s) s)
    (hA : ∀ᶠ s in 𝓝 (x 0), a s ≠ 0)
    (hd2 : HasDerivAt a₁ (a₂ (x 0)) (x 0)) (i : Fin 4) (hi : i ≠ 0) :
    einstein (flrwMetric a) x i i = -(2 * a (x 0) * a₂ (x 0) + a₁ (x 0) ^ 2) :=
  GRLab.friedmann_second hD hA hd2 i hi

theorem einstein_flrw_offDiag {a a₁ a₂ : ℝ → ℝ} {x : Fin 4 → ℝ}
    (hD : ∀ᶠ s in 𝓝 (x 0), HasDerivAt a (a₁ s) s)
    (hA : ∀ᶠ s in 𝓝 (x 0), a s ≠ 0)
    (hd2 : HasDerivAt a₁ (a₂ (x 0)) (x 0)) (b d : Fin 4) (h : b ≠ d) :
    einstein (flrwMetric a) x b d = 0 :=
  GRLab.einstein_flrw_offDiag hD hA hd2 b d h

/-! ## Part IX — static de Sitter: theorems -/

theorem ricci_deSitterStatic {L : ℝ} {x : Fin 4 → ℝ} (hL : L ≠ 0) (hx : x ∈ DSRegion L)
    (b d : Fin 4) :
    ricci (deSitterStatic L) x b d = (3 / L ^ 2) * deSitterStatic L x b d :=
  GRLab.ricci_deSitterStatic hL hx b d

theorem deSitterStatic_scalarCurvature {L : ℝ} {x : Fin 4 → ℝ} (hL : L ≠ 0)
    (hx : x ∈ DSRegion L) : scalarCurvature (deSitterStatic L) x = 12 / L ^ 2 :=
  GRLab.deSitterStatic_scalarCurvature hL hx

/-! ## Part X — Minkowski in spherical coordinates: theorem -/

theorem minkowskiSpherical_ricciFlat {x : Fin 4 → ℝ} (hr : x 1 ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) : RicciFlatAt minkowskiSpherical x :=
  GRLab.minkowskiSpherical_ricciFlat hr hs

/-! ## Part XI — Kiselev: theorems -/

theorem ricci_kiselev_thetaTheta {M c w : ℝ} {x : Fin 4 → ℝ} (hr : 0 < x 1)
    (hs : Real.sin (x 2) ≠ 0)
    (hF : ∀ᶠ s in 𝓝 (x 1), kiselevF M c w s ≠ 0) :
    ricci (kiselev M c w) x 2 2 = -(3 * w * c * (x 1) ^ (-(3 * w + 1))) :=
  GRLab.ricci_kiselev_thetaTheta hr hs hF

theorem kiselev_ricciFlat_of_w_eq_zero {M c : ℝ} {x : Fin 4 → ℝ} (hr : 0 < x 1)
    (hs : Real.sin (x 2) ≠ 0)
    (hF : ∀ᶠ s in 𝓝 (x 1), kiselevF M c 0 s ≠ 0) :
    RicciFlatAt (kiselev M c 0) x :=
  GRLab.kiselev_ricciFlat_of_w_eq_zero hr hs hF

end SchwarzschildVacuum
