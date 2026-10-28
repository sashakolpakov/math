import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.StructureDimension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.EulerIndex
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroTensorPowers
import OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial

/-! # Tensor Powers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorPowers.ProjectiveK

noncomputable section

/-! The tensor endomorphism of coherent K-theory acts by the genuine
line-bundle powers. Its Euler orbits have intrinsic degree bounds. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroTensorPowers
open OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial

universe u
attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

theorem coherentTensorEnd_power {A : Scheme.{u}} (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (n : ℕ) :
    (KTheory.Projective.coherentTensorEnd L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)) ^ n =
      KTheory.Projective.coherentTensorEnd (L.tensorPower n).sheaf
        (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible (L.tensorPower n)) := by
  induction n with
  | zero =>
      have he : (L.tensorPower 0).sheaf ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj A := L.tensorPowerZeroIso
      exact ((KTheory.Projective.coherentTensorK0_congr _ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit he).trans
        (KTheory.Projective.coherentTensorK0_unit A)).symm
  | succ n ih =>
      rw [pow_succ', ih]
      change (KTheory.Projective.coherentTensorK0 L.sheaf _).comp
        (KTheory.Projective.coherentTensorK0 (L.tensorPower n).sheaf _) = _
      rw [KTheory.Projective.coherentTensorK0_comp]
      apply KTheory.Projective.coherentTensorK0_congr
      exact AlgebraicGeometry.Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.tensorIso _ _ ≪≫
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) L.tensorPowerOneIso.symm ≪≫
          (AlgebraicGeometry.Quotients.FiniteDescent.TensorPower.Construction.TensorPowerAddition.iso L.sheaf n 1).symm

variable {K : Type u} [Field K] {r : ℕ} {A : Scheme.{u}}
  (f : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
  [IsClosedImmersion f]

theorem coherentEulerIndex_tensor_power_structure (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) (n : ℕ) :
    EulerIndex.ProjectiveK.coherentEulerIndex f
      ((KTheory.Projective.coherentTensorEnd L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L) ^ n)
        (KTheory.Projective.coherentK0Class (StructureDimension.ProjectiveK.coherentStructureModule A))) =
      EulerIndex.ProjectiveK.coherentEuler f (L.tensorPower n).sheaf := by
  rw [coherentTensorEnd_power]
  change EulerIndex.ProjectiveK.coherentEulerIndex f
    (KTheory.Projective.coherentTensorK0 (L.tensorPower n).sheaf _
      (KTheory.Projective.coherentK0Class (StructureDimension.ProjectiveK.coherentStructureModule A))) = _
  rw [EulerIndex.ProjectiveK.coherentEulerIndex_tensor_class]
  exact EulerIndex.ProjectiveK.coherentEuler_eq_of_iso f (AlgebraicGeometry.SheafCohomology.Projective.PolynomialQuotient.Dimension.structureModuleTensorLeftIso _)

variable [IsIntegral A] [Infinite K]

theorem lineBundle_tensorPower_euler_polynomial (j : Fin (r + 1))
    (ρ : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType ρ] (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ ∧
      ∀ n : ℕ, P.eval (n : ℚ) = (EulerIndex.ProjectiveK.coherentEuler f (L.tensorPower n).sheaf : ℚ) := by
  let T := KTheory.Projective.coherentTensorEnd L.sheaf (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)
  let x := KTheory.Projective.coherentK0Class (StructureDimension.ProjectiveK.coherentStructureModule A)
  let d := AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ρ
  have hT : ((T - 1) ^ (d + 1)) x = 0 :=
    StructureDimension.ProjectiveK.coherentTensorDifference_structure_dimension f j ρ L.sheaf
      (AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible L)
  refine ⟨AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial T (EulerIndex.ProjectiveK.coherentEulerIndex f) x (d + 1), ?_, fun n => ?_⟩
  · simpa only [Nat.add_sub_cancel] using
      AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial_natDegree_le T (EulerIndex.ProjectiveK.coherentEulerIndex f) x (d + 1)
  · rw [AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial_eval_of_apply_eq_zero T (EulerIndex.ProjectiveK.coherentEulerIndex f) x
      (d + 1) hT]
    exact congrArg (fun z : ℤ => (z : ℚ)) (coherentEulerIndex_tensor_power_structure f L n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Coherent.TensorPowers.ProjectiveK
