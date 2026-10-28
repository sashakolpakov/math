import OAI.AlgebraicGeometry.Comparison.Betti.Closed.FormAntiholomorphicDirections
import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionAnticommutation
import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalDirections
import OAI.AlgebraicGeometry.Comparison.Betti.Pure.VectorCauchy

/-! # Contraction Cauchy Primitive -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ContractionCauchyPrimitive.Dolbeault

noncomputable section

section

/-! The coefficient to which the actual one-coordinate Cauchy operator
is applied in any form degree. Closedness supplies the preserved directions. -/

open _root_.TopologicalSpace Set
open scoped ContDiff _root_.Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P]

def productOpen (S : Opens P) (U : Opens ℂ) : Opens (P × ℂ) :=
  ⟨(S : Set P) ×ˢ (U : Set ℂ), S.isOpen.prod U.isOpen⟩

variable {S : Opens P} {U : Opens ℂ}

def lastContractionCoefficient (n : ℕ) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1))
    (p : P) (w : ℂ) : Analysis.DifferentialForms.Manifold.Basic.FormValue (P × ℂ) n :=
  AntiholomorphicContraction.Dolbeault.antiContraction n (0, 1) (a.extension (p, w))

omit [IsScalarTower ℝ ℂ P] in
theorem lastContractionCoefficient_smooth (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1)) :
    ContDiffOn ℝ ∞ (Function.uncurry (lastContractionCoefficient n a))
      ((S : Set P) ×ˢ (U : Set ℂ)) :=
  ((AntiholomorphicContraction.Dolbeault.antiContraction (E := P × ℂ) n (0, 1)).restrictScalars ℝ).contDiff.comp_contDiffOn a.smooth

theorem lastContractionCoefficient_holomorphic_direction (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1))
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0) (v : P)
    (hv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (productOpen S U) n (v, 0) a = 0)
    (x : P × ℂ) (hx : x.1 ∈ S) (w : ℂ) (hw : w ∈ U) :
    fderiv ℝ (Function.uncurry (lastContractionCoefficient n a)) (x.1, w) (Complex.I • v, 0) =
      Complex.I • fderiv ℝ (Function.uncurry (lastContractionCoefficient n a)) (x.1, w) (v, 0) := by
  have h := Closed.FormAntiholomorphicDirections.Dolbeault.closed_openForm_contraction_antiDerivative_zero n (v, 0) (0, 1) a ha hv
    ⟨(x.1, w), ⟨hx, hw⟩⟩
  have he := (VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative_eq_zero_iff
    (Function.uncurry (lastContractionCoefficient n a)) (x.1, w) (v, 0)).mp h
  simpa only [Prod.smul_mk, smul_eq_mul, mul_zero] using he

omit [IsScalarTower ℝ ℂ P] in
theorem lastContractionCoefficient_kernel (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 2)) (v : P × ℂ)
    (hv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (productOpen S U) (n + 1) v a = 0)
    (p : P) (hp : p ∈ S) (w : ℂ) (hw : w ∈ U) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v (lastContractionCoefficient (n + 1) a p w) = 0 := by
  apply AntiholomorphicContractionAnticommutation.Dolbeault.antiContraction_preserves_kernel
  have he := congrArg (fun b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1) =>
    b ⟨(p, w), ⟨hp, hw⟩⟩) hv
  change AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v (a.extension (p, w)) = 0
  rw [show a.extension (p, w) = a ⟨(p, w), ⟨hp, hw⟩⟩ from
    a.extension_apply ⟨(p, w), ⟨hp, hw⟩⟩]
  simpa only [Open.AntiholomorphicContraction.Dolbeault.openAntiContraction_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply] using he

omit [IsScalarTower ℝ ℂ P] in
theorem lastContractionCoefficient_last_kernel (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 2)) (p : P) (w : ℂ) :
    AntiholomorphicContraction.Dolbeault.antiContraction n (0, 1) (lastContractionCoefficient (n + 1) a p w) = 0 :=
  AntiholomorphicContractionAnticommutation.Dolbeault.antiContraction_squared n (0, 1) (a.extension (p, w))

theorem lastContractionCoefficient_pure (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (p + q + 1))
    (ha : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a)
    (x : P) (hx : x ∈ S) (w : ℂ) (hw : w ∈ U) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (P × ℂ) p q (lastContractionCoefficient (p + q) a x w) := by
  apply AntiholomorphicContractionPurity.Dolbeault.antiContraction_pure
  rw [show a.extension (x, w) = a ⟨(x, w), ⟨hx, hw⟩⟩ from
    a.extension_apply ⟨(x, w), ⟨hx, hw⟩⟩]
  exact ha ⟨(x, w), ⟨hx, hw⟩⟩

end

/-! The actual Cauchy primitive of a contracted form, with simultaneous
preservation of pure type, contraction kernels, and holomorphic directions. -/

open _root_.TopologicalSpace Set
open scoped ContDiff _root_.Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] {S : Opens P} {U : Opens ℂ}

def contractionCauchyPrimitive (n : ℕ) (χ : ℂ → ℝ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1)) : P × ℂ → Analysis.DifferentialForms.Manifold.Basic.FormValue (P × ℂ) n :=
  VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform χ (lastContractionCoefficient n a)

variable {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hsub : tsupport χ ⊆ (U : Set ℂ))

include hχ hc hsub

omit [IsScalarTower ℝ ℂ P] in
theorem contractionCauchyPrimitive_smooth (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1)) :
    ContDiffOn ℝ ∞ (contractionCauchyPrimitive n χ a) ((S : Set P) ×ˢ univ) :=
  VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform_smooth hχ hc S.isOpen U.isOpen hsub
    (lastContractionCoefficient_smooth n a)

theorem contractionCauchyPrimitive_last_derivative (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1))
    (x : P × ℂ) (hx : x.1 ∈ S) (hχx : χ x.2 = 1) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative (contractionCauchyPrimitive n χ a) x (0, 1) =
      lastContractionCoefficient n a x.1 x.2 := by
  have hd : DifferentiableAt ℝ (contractionCauchyPrimitive n χ a) (x.1, x.2) :=
    ((contractionCauchyPrimitive_smooth hχ hc hsub n a).contDiffAt
      ((S.isOpen.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)).differentiableAt (by simp)
  rw [← VectorAntiholomorphicDerivative.Dolbeault.vectorDbar_product_slice hd]
  exact VectorCauchyLocalPrimitive.Dolbeault.localizedVectorCauchyTransform_primitive hχ hc S.isOpen U.isOpen hsub
    (lastContractionCoefficient_smooth n a) hx hχx

theorem contractionCauchyPrimitive_pure (n p q : ℕ) (hn : n = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1))
    (ha : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (x : P × ℂ) (hx : x.1 ∈ S) :
    ∀ (z : ℂˣ) (v : Fin n → P × ℂ),
      contractionCauchyPrimitive n χ a x (fun i => (z : ℂ) • v i) =
        Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * contractionCauchyPrimitive n χ a x v := by
  subst n
  exact Pure.VectorCauchy.Dolbeault.localizedVectorCauchyTransform_pure p q hχ hc S.isOpen U.isOpen hsub
    (lastContractionCoefficient_smooth (p + q) a) x hx
      (lastContractionCoefficient_pure p q a ha x.1 hx)

omit [IsScalarTower ℝ ℂ P] in
theorem contractionCauchyPrimitive_last_kernel (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 2)) (x : P × ℂ) (hx : x.1 ∈ S) :
    AntiholomorphicContraction.Dolbeault.antiContraction n (0, 1) (contractionCauchyPrimitive (n + 1) χ a x) = 0 :=
  VectorCauchyLocalNaturality.Dolbeault.localizedVectorCauchyTransform_kernel (AntiholomorphicContraction.Dolbeault.antiContraction n (0, 1))
    hχ hc S.isOpen U.isOpen hsub (lastContractionCoefficient_smooth (n + 1) a) x hx
      (fun w _ => lastContractionCoefficient_last_kernel n a x.1 w)

omit [IsScalarTower ℝ ℂ P] in
theorem contractionCauchyPrimitive_kernel (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 2)) (v : P × ℂ)
    (hv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (productOpen S U) (n + 1) v a = 0)
    (x : P × ℂ) (hx : x.1 ∈ S) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v (contractionCauchyPrimitive (n + 1) χ a x) = 0 :=
  VectorCauchyLocalNaturality.Dolbeault.localizedVectorCauchyTransform_kernel (AntiholomorphicContraction.Dolbeault.antiContraction n v)
    hχ hc S.isOpen U.isOpen hsub (lastContractionCoefficient_smooth (n + 1) a) x hx
      (lastContractionCoefficient_kernel n a v hv x.1 hx)

theorem contractionCauchyPrimitive_preserves_direction (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (productOpen S U) (n + 1))
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0) (v : P)
    (hv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (productOpen S U) n (v, 0) a = 0)
    (x : P × ℂ) (hx : x.1 ∈ S) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative (contractionCauchyPrimitive n χ a) x (v, 0) = 0 := by
  apply (VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative_eq_zero_iff _ _ _).mpr
  have h := VectorCauchyLocalDirections.Dolbeault.localizedVectorCauchyTransform_preserves_holomorphic_direction
    hχ hc S.isOpen U.isOpen hsub (lastContractionCoefficient_smooth n a) x hx v
      (lastContractionCoefficient_holomorphic_direction n a ha v hv x hx)
  simpa only [contractionCauchyPrimitive, Prod.smul_mk, smul_eq_mul, mul_zero] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.ContractionCauchyPrimitive.Dolbeault
