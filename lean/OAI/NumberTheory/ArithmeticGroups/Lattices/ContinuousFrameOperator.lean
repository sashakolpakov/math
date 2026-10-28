import OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.TensorStabilizer
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Continuous Frame Operator -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousFrameOperator.Construction

noncomputable section

/-! Continuous faithful operator coordinates for the general linear group. -/

open scoped Classical
open _root_.Module

theorem continuous_finite_operator_family
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : X → E →L[ℝ] E) (hf : ∀ x, Continuous (fun g => f g x)) : Continuous f :=
  continuous_clm_apply.mpr hf

def continuousFrameOperator
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) (g : Matrix.GeneralLinearGroup ι ℝ) :
    E →L[ℝ] E := (LatticeFrameAction.Construction.matrixFrameAction b g).toLinearMap.toContinuousLinearMap

theorem continuousFrameOperator_apply
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) (g : Matrix.GeneralLinearGroup ι ℝ) (x : E) :
    continuousFrameOperator b g x = LatticeFrameAction.Construction.matrixFrameAction b g x := rfl

theorem continuous_continuousFrameOperator
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) : Continuous (continuousFrameOperator b) := by
  let l : Matrix ι ι ℝ →ₗ[ℝ] (E →L[ℝ] E) :=
    (LinearMap.toContinuousLinearMap : Module.End ℝ E ≃ₗ[ℝ] (E →L[ℝ] E)).toLinearMap.comp
      (Matrix.toLin b b).toLinearMap
  have he : continuousFrameOperator b = fun g => l g.val := by
    funext g
    apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun (LatticeFrameAction.Construction.matrixFrameAction_toLinearMap b g) x
  rw [he]
  exact l.continuous_of_finiteDimensional.comp Units.continuous_val

theorem continuousFrameOperator_one
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) : continuousFrameOperator b 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change LatticeFrameAction.Construction.matrixFrameAction b 1 x = x
  rw [map_one]
  rfl

theorem continuousFrameOperator_injective
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) : Function.Injective (continuousFrameOperator b) := by
  intro g h he
  apply (LatticeFrameAction.Construction.matrixFrameAction b).injective
  apply LinearEquiv.ext
  intro x
  exact DFunLike.congr_fun he x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousFrameOperator.Construction
