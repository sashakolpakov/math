import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CoordinateLineCauchy
import OAI.AlgebraicGeometry.Comparison.Betti.ContractionCauchyPrimitive

/-! # Line Contraction Primitive -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineContractionPrimitive.Dolbeault

noncomputable section

/-! Global primitives of contracted forms on ordinary or punctured
coordinate lines, with the original pure type and contraction kernels. -/

open _root_.TopologicalSpace Set
open scoped ContDiff _root_.Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]

def coordinateLineContractionPrimitive (S : Opens P) (b : Bool) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) (n + 1)) : P × ℂ → Analysis.DifferentialForms.Manifold.Basic.FormValue (P × ℂ) n :=
  PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate S b (Function.uncurry (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient n a))
    (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_smooth n a)

theorem coordinateLineContractionPrimitive_smooth (S : Opens P) (b : Bool) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) (n + 1)) :
    ContDiffOn ℝ ∞ (coordinateLineContractionPrimitive S b n a)
      ((S : Set P) ×ˢ (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b : Set ℂ)) :=
  PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_smooth S b _ (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_smooth n a)

theorem coordinateLineContractionPrimitive_last_derivative (S : Opens P) (b : Bool) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) (n + 1))
    (x : P × ℂ) (hx : x ∈ ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative (coordinateLineContractionPrimitive S b n a) x (0, 1) =
      ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient n a x.1 x.2 := by
  have hd : DifferentiableAt ℝ (coordinateLineContractionPrimitive S b n a) (x.1, x.2) :=
    ((coordinateLineContractionPrimitive_smooth S b n a).contDiffAt
      ((S.isOpen.prod (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b).isOpen).mem_nhds hx)).differentiableAt (by simp)
  rw [← VectorAntiholomorphicDerivative.Dolbeault.vectorDbar_product_slice hd]
  exact PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_dbar S b _ (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_smooth n a) hx.1 hx.2

theorem coordinateLineContractionPrimitive_pure (S : Opens P) (b : Bool) (n p q : ℕ) (hn : n = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) (n + 1))
    (ha : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (x : P × ℂ) (hx : x.1 ∈ S) :
    ∀ (z : ℂˣ) (v : Fin n → P × ℂ),
      coordinateLineContractionPrimitive S b n a x (fun i => (z : ℂ) • v i) =
        Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * coordinateLineContractionPrimitive S b n a x v := by
  subst n
  exact Pure.CoordinateLineCauchy.Dolbeault.coordinateLineCauchyCandidate_pure S b p q _ (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_smooth (p + q) a) x hx
    (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_pure p q a ha x.1 hx)

theorem coordinateLineContractionPrimitive_last_kernel (S : Opens P) (b : Bool) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) (n + 2)) (x : P × ℂ) (hx : x.1 ∈ S) :
    AntiholomorphicContraction.Dolbeault.antiContraction n (0, 1) (coordinateLineContractionPrimitive S b (n + 1) a x) = 0 :=
  PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_kernel (AntiholomorphicContraction.Dolbeault.antiContraction n (0, 1)) S b _
    (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_smooth (n + 1) a) x hx
    (fun w _ => ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_last_kernel n a x.1 w)

theorem coordinateLineContractionPrimitive_kernel (S : Opens P) (b : Bool) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) (n + 2)) (v : P × ℂ)
    (hv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) (n + 1) v a = 0)
    (x : P × ℂ) (hx : x.1 ∈ S) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v (coordinateLineContractionPrimitive S b (n + 1) a x) = 0 :=
  PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_kernel (AntiholomorphicContraction.Dolbeault.antiContraction n v) S b _
    (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_smooth (n + 1) a) x hx
    (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_kernel n a v hv x.1 hx)

theorem coordinateLineContractionPrimitive_preserves_direction (S : Opens P) (b : Bool) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) (n + 1))
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) a = 0) (v : P)
    (hv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) n (v, 0) a = 0)
    (x : P × ℂ) (hx : x ∈ ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b)) :
    VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative (coordinateLineContractionPrimitive S b n a) x (v, 0) = 0 := by
  apply (VectorAntiholomorphicDerivative.Dolbeault.vectorAntiDerivative_eq_zero_iff _ _ _).mpr
  have h := PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_preserves_direction S b _ (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_smooth n a)
    x hx v (ContractionCauchyPrimitive.Dolbeault.lastContractionCoefficient_holomorphic_direction n a ha v hv x hx.1)
  simpa only [coordinateLineContractionPrimitive, Prod.smul_mk, smul_eq_mul, mul_zero] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineContractionPrimitive.Dolbeault
