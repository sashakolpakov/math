import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseLimitCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineResidueInjection

/-! # Crystalline Residue Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineResidueCoordinates

noncomputable section

/-! The native Čech residue evaluation is the original integral crystalline restriction at level zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

theorem coordinate (i n : ℕ) (x : Witt.Crystalline.integralCohomology p k X i) :
    WittCechLinearEquiv.equivalence p k X n i
      ((CechInverseLimit.integralEquiv p k X hprojective i x).val n) =
        BoundedCrystalline.CrystallineCohomology.restriction f n i
          ((Global.Crystalline.Comparison.integralEquiv p k X i).symm x) := by
  let := CrystallineInverseLimit.inclusion_mono p k X hprojective i
  let e := WittCechLinearEquiv.equivalence p k X n i
  let y := (Global.Crystalline.Comparison.integralEquiv p k X i).symm x
  change e (e.symm ((CrystallineInverseLimit.bigCompatibleEquiv p k X hprojective i y).val n)) = _
  exact (e.apply_symm_apply _).trans (Crystalline.InverseLimitCoordinates.compatible_coordinate f i y n)

theorem evaluation (x : Witt.Crystalline.integralCohomology p k X 0) :
    CrystallineResidueInjection.integralEvaluation p k X hprojective x =
      ZeroLevel.GlobalFunctionLinear.cohomologyMap p k X
        (BoundedCrystalline.CrystallineCohomology.restriction f 0 0
          ((Global.Crystalline.Comparison.integralEquiv p k X 0).symm x)) :=
  congrArg (ZeroLevel.GlobalFunctionLinear.cohomologyMap p k X) (coordinate p k X hprojective 0 0 x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineResidueCoordinates
