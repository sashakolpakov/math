import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineResidueCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.SectionRestriction

/-! # Residue Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.ResidueEvaluation

noncomputable section

/-! The original integral crystalline residue is surjective onto actual global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

theorem evaluation (w : WittVector p A) :
    SmoothProper.CrystallineResidueInjection.integralEvaluation p k X hprojective
      (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w) = ULift.up (w.coeff 0) := by
  let e := Global.Crystalline.Comparison.integralEquiv p k X 0
  let b := SmoothProper.GlobalFunctionConstants.bigMap p k X hprojective w
  have hi : e.symm (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w) = b :=
    e.symm_apply_apply b
  have h₀ := SmoothProper.CrystallineResidueCoordinates.evaluation p k X hprojective
    (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w)
  have h₁ := congrArg (ZeroLevel.GlobalFunctionLinear.cohomologyMap p k X)
    (congrArg (BoundedCrystalline.CrystallineCohomology.restriction f 0 0) hi)
  have h₂ := BoundedCrystalline.SectionRestriction.cohomology f 0 b
  have h₃ := congrArg (BoundedCrystalline.CrystallineSections.restriction f 0)
    (SmoothProper.GlobalFunctionConstants.bigMap_sections p k X hprojective w)
  have h₄ := congrArg (ZeroLevel.GlobalFunctionLinear.sectionsMap p k X) (h₂.trans h₃)
  exact h₀.trans (h₁.trans (h₄.trans (congrArg ULift.up
    (WittResidue.global_value p k X hprojective w))))

theorem surjective : Function.Surjective
    (SmoothProper.CrystallineResidueInjection.integralEvaluation p k X hprojective) := by
  intro a
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective (R := A) p a.down
  refine ⟨SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w, ?_⟩
  exact (evaluation p k X hprojective w).trans (congrArg ULift.up hw)

theorem residue_bijective : Function.Bijective
    (SmoothProper.CrystallineResidueInjection.map p k X hprojective) := by
  refine ⟨SmoothProper.CrystallineResidueInjection.injective p k X hprojective, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := surjective p k X hprojective a
  exact ⟨Submodule.Quotient.mk x, hx⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.ResidueEvaluation
