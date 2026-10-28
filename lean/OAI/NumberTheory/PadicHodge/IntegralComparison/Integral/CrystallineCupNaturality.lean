import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.PullbackRestriction

/-! # Crystalline Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCupNaturality

noncomputable section

/-! The original integral crystalline cup is natural for actual geometric
maps. Equality is detected by the proved native bounded restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCup

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "hg" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement.over_witt p k X Y g

/-- Transport of the genuine geometric Ext map through the established
big-to-small crystalline equivalence. -/
def pullback (i : ℕ) : Witt.Crystalline.integralCohomology p k Y i →ₗ[R] Witt.Crystalline.integralCohomology p k X i :=
  (Global.Crystalline.Comparison.integralEquiv p k X i).toLinearMap.comp
    ((BigCrystallineCohomology.pullback g.left hg i).comp
      (Global.Crystalline.Comparison.integralEquiv p k Y i).symm.toLinearMap)

omit [Fintype k] [Smooth X.hom] [Smooth Y.hom] in
theorem restriction_pullback (n i : ℕ) (x : Witt.Crystalline.integralCohomology p k Y i) :
    CrystallineCup.restriction p k X n i (pullback p k X Y g i x) =
      BoundedCrystalline.CrystallinePullback.pullback g.left hg n i (CrystallineCup.restriction p k Y n i x) := by
  change BoundedCrystalline.CrystallineCohomology.restriction (Witt.Crystalline.wittStructureMap p k X) n i
    ((Global.Crystalline.Comparison.integralEquiv p k X i).symm
      ((Global.Crystalline.Comparison.integralEquiv p k X i)
        (BigCrystallineCohomology.pullback g.left hg i
          ((Global.Crystalline.Comparison.integralEquiv p k Y i).symm x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (BoundedCrystalline.PullbackRestriction.naturality g.left hg n i
    ((Global.Crystalline.Comparison.integralEquiv p k Y i).symm x)).symm

variable (hX : Projectivity.Construction.ProjectiveOver k X.hom) (hY : Projectivity.Construction.ProjectiveOver k Y.hom)

theorem cup_natural (i j : ℕ) (x : Witt.Crystalline.integralCohomology p k Y i) (y : Witt.Crystalline.integralCohomology p k Y j) :
    pullback p k X Y g (i + j) (CrystallineCup.cup p k Y hY i j x y) =
      CrystallineCup.cup p k X hX i j (pullback p k X Y g i x) (pullback p k X Y g j y) := by
  apply (CrystallineCup.equivalence p k X hX (i + j)).injective
  apply Subtype.ext
  funext n
  rw [CrystallineCup.equivalence_coordinate, CrystallineCup.equivalence_coordinate,
    restriction_pullback, CrystallineCup.restriction_cup, CrystallineCup.restriction_cup,
    restriction_pullback, restriction_pullback]
  exact SmoothProper.WittGeometricCupNaturality.cup_natural p k X Y g n i j
    (CrystallineCup.restriction p k Y n i x) (CrystallineCup.restriction p k Y n j y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCupNaturality
