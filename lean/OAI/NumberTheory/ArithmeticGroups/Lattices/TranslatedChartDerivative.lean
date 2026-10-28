import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Translated Chart Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.TranslatedChartDerivative.Construction

noncomputable section

/-! Derivatives of translations in a global chart follow from the
factorization of its ambient derivative into translation and tangent coordinates. -/

open scoped _root_.Topology

theorem translated_chart_hasFDerivAt
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedRing A] [NormedAlgebra ℝ A]
    (i : E →L[ℝ] A) (hi : Function.Injective i)
    (f : E → A) (J : E → E ≃L[ℝ] E)
    (hf : ∀ x, HasFDerivAt f
      ((ContinuousLinearMap.mul ℝ A (f x)).comp (i.comp (J x).toContinuousLinearMap)) x)
    (hunit : ∀ x, IsUnit (f x))
    (e : E ≃ₜ E) (g : A) (he : ∀ x, f (e x) = g * f x) (x : E) :
    HasFDerivAt e ((J (e x)).symm.toContinuousLinearMap.comp (J x).toContinuousLinearMap) x := by
  let D : E → E →L[ℝ] A := fun y =>
    (ContinuousLinearMap.mul ℝ A (f y)).comp (i.comp (J y).toContinuousLinearMap)
  have hinj : Function.Injective (D (e x)) := by
    intro u v huv
    apply (J (e x)).injective
    apply hi
    exact (hunit (e x)).mul_right_injective huv
  have hemb : Topology.IsEmbedding (D (e x)) :=
    (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)).isEmbedding
  have hd := (ContinuousLinearMap.mul ℝ A g).hasFDerivAt.comp x (hf x)
  have hcomp : (ContinuousLinearMap.mul ℝ A g).comp (D x) =
      (D (e x)).comp ((J (e x)).symm.toContinuousLinearMap.comp (J x).toContinuousLinearMap) := by
    ext y
    change g * (f x * i (J x y)) = f (e x) * i (J (e x) ((J (e x)).symm (J x y)))
    rw [(J (e x)).apply_symm_apply, he, mul_assoc]
  change HasFDerivAt (fun y => g * f y) ((ContinuousLinearMap.mul ℝ A g).comp (D x)) x at hd
  rw [hcomp] at hd
  exact HasFDerivAt.of_comp_of_isEmbedding e.continuous.continuousAt (hf (e x)) hemb hd
    (Filter.Eventually.of_forall he)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.TranslatedChartDerivative.Construction
