import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.ResidueEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.ResidueLiftingSurjectivity

/-! # Crystalline Generation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineGeneration

noncomputable section

/-! The canonical global-function classes generate original integral crystalline H⁰ in its original coefficient module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X 0

def coefficientMap : Crystalline.EtaleSections.source (B := W) (WittVector p A) →ₗ[R] M := by
  let := SmoothProper.GlobalFunctionWitt.etale p k X hprojective
  exact (Global.Crystalline.Comparison.integralEquiv p k X 0).toLinearMap.comp
    (Crystalline.EtaleSections.cohomologyMap (WittVector p A)
      (WittFactor.factor k X p) (WittFactor.overBase k X p))

theorem coefficientMap_apply (w : WittVector p A) :
    coefficientMap p k X hprojective (ULift.up w) =
      SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w := rfl

theorem residue_surjective : ∀ x : ZeroLevel.GlobalFunctionLinear.coefficientModule p k X,
    ∃ w : Crystalline.EtaleSections.source (B := W) (WittVector p A),
      SmoothProper.CrystallineResidueInjection.integralEvaluation p k X hprojective
        (coefficientMap p k X hprojective w) = x := by
  intro x
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective («R» := A) p x.down
  refine ⟨ULift.up w, ?_⟩
  have h₁ := congrArg (SmoothProper.CrystallineResidueInjection.integralEvaluation p k X hprojective)
    (coefficientMap_apply p k X hprojective w)
  have h₂ := ResidueEvaluation.evaluation p k X hprojective w
  have h₃ : (ULift.up (w.coeff 0) : ZeroLevel.GlobalFunctionLinear.coefficientModule p k X) = x := by
    apply ULift.ext
    exact hw
  exact h₁.trans (h₂.trans h₃)

theorem lifts (x : M) : ∃ w : Crystalline.EtaleSections.source (B := W) (WittVector p A),
    coefficientMap p k X hprojective w - x ∈ (Ideal.span {(p : R)}) • (⊤ : Submodule R M) := by
  have hk := SmoothProper.CrystallineResidueInjection.integralEvaluation_kernel p k X hprojective
  obtain ⟨w, hw⟩ := residue_surjective p k X hprojective
    (SmoothProper.CrystallineResidueInjection.integralEvaluation p k X hprojective x)
  refine ⟨w, ?_⟩
  rw [← hk, LinearMap.mem_ker, map_sub]
  exact sub_eq_zero.mpr hw

theorem coefficient_surjective : Function.Surjective (coefficientMap p k X hprojective) := by
  have hs := lifts p k X hprojective
  let : Module.Finite R M := SmoothProper.CrystallineFiniteness.integral_coefficient p k X hprojective 0
  let : IsAdicComplete (Ideal.span {(p : R)}) R := Witt.Coefficient.coefficient p k
  exact @ResidueLiftingSurjectivity.surjective_of_lifts R inferInstance
    (Crystalline.EtaleSections.source (B := W) (WittVector p A)) inferInstance inferInstance
    M inferInstance inferInstance inferInstance
    (Ideal.span {(p : R)}) (IsAdicComplete.le_jacobson_bot _)
    (coefficientMap p k X hprojective) hs

theorem surjective : Function.Surjective (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective) := by
  intro x
  obtain ⟨w, hw⟩ := coefficient_surjective p k X hprojective x
  exact ⟨w.down, (coefficientMap_apply p k X hprojective w.down).symm.trans hw⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineGeneration
