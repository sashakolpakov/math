import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerHilbert
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrbitLeadingCoefficient

/-! # Hilbert Leading Difference -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.HilbertLeadingDifference.ProjectiveK

noncomputable section

/-! The top tensor difference of the structure sheaf computes the
positive leading coefficient of its actual Hilbert polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.OrbitLeadingCoefficient.ProjectiveCohomologyProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] [Infinite K] {r : ℕ} {A : Scheme.{u}} [IsIntegral A]
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f] (j : Fin (r + 1))

theorem coherentStructureHilbert_leadingCoeff_eq_difference
    (ρ : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType ρ] :
    (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j (StructureDimension.ProjectiveK.coherentStructureModule A)).leadingCoeff =
      (EulerIndex.ProjectiveK.coherentEulerIndex f
        ((KTheory.Projective.coherentTensorDifference (EulerHilbert.ProjectiveK.projectiveLineBundle f j).sheaf
          (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (EulerHilbert.ProjectiveK.projectiveLineBundle f j)) ^
            AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ)
              (KTheory.Projective.coherentK0Class (StructureDimension.ProjectiveK.coherentStructureModule A))) : ℚ) /
        ((AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ).factorial : ℚ) := by
  let M := StructureDimension.ProjectiveK.coherentStructureModule A
  let T := KTheory.Projective.coherentTensorEnd (EulerHilbert.ProjectiveK.projectiveLineBundle f j).sheaf
    (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (EulerHilbert.ProjectiveK.projectiveLineBundle f j))
  let d := AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ
  let x := KTheory.Projective.coherentK0Class M
  have hT : ((T - 1) ^ (d + 1)) x = 0 :=
    StructureDimension.ProjectiveK.coherentTensorDifference_structure_dimension f j ρ
      (EulerHilbert.ProjectiveK.projectiveLineBundle f j).sheaf
      (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (EulerHilbert.ProjectiveK.projectiveLineBundle f j))
  let P := AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial T (EulerIndex.ProjectiveK.coherentEulerIndex f) x (d + 1)
  have he : HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M = P := by
    apply AlgebraicGeometry.FormalGeometry.Completion.EventualPolynomial.Construction.polynomial_eq_of_eventual_nat_eval _ _ 0
    intro n _
    rw [EulerHilbert.ProjectiveK.coherentHilbertPolynomial_eval_eq_euler_orbit]
    exact (AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial_eval_of_apply_eq_zero T
      (EulerIndex.ProjectiveK.coherentEulerIndex f) x (d + 1) hT n).symm
  have hdeg : (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M).natDegree = d :=
    (StructureDimension.ProjectiveK.coherentStructureHilbertPolynomial_dimension f j ρ).1
  calc
    (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M).leadingCoeff =
        (HilbertFiltration.ProjectiveK.coherentHilbertPolynomial f j M).coeff d := by rw [← hdeg, Polynomial.coeff_natDegree]
    _ = P.coeff d := congrArg (fun Q : Polynomial ℚ => Q.coeff d) he
    _ = _ := OrbitLeadingCoefficient.ProjectiveCohomologyProjective.endomorphismOrbitPolynomial_coeff_top T (EulerIndex.ProjectiveK.coherentEulerIndex f) x d

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.HilbertLeadingDifference.ProjectiveK
