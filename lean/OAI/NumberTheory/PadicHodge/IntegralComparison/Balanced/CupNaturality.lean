import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CrystallineCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittGeometricCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.PullbackRestriction

/-! # Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupNaturality.Integral

noncomputable section

/-! The original integral crystalline cup is natural for actual geometric
maps. Equality is detected by the proved native bounded restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CrystallineCup.Integral

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "hg" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement.over_witt p k X Y g

open OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCupNaturality (pullback)

omit [Fintype k] [Smooth X.hom] [Smooth Y.hom] in
theorem restriction_pullback (n i : ℕ) (x : Witt.Crystalline.integralCohomology p k Y i) :
    CrystallineCup.Integral.restriction p k X n i (Integral.CrystallineCupNaturality.pullback p k X Y g i x) =
      BoundedCrystalline.CrystallinePullback.pullback g.left hg n i (CrystallineCup.Integral.restriction p k Y n i x) :=
  Integral.CrystallineCupNaturality.restriction_pullback p k X Y g n i x

variable (hX : Projectivity.Construction.ProjectiveOver k X.hom) (hY : Projectivity.Construction.ProjectiveOver k Y.hom)

theorem cup_natural (i j : ℕ) (x : Witt.Crystalline.integralCohomology p k Y i) (y : Witt.Crystalline.integralCohomology p k Y j) :
    Integral.CrystallineCupNaturality.pullback p k X Y g (i + j) (CrystallineCup.Integral.cup p k Y hY i j x y) =
      CrystallineCup.Integral.cup p k X hX i j (Integral.CrystallineCupNaturality.pullback p k X Y g i x) (Integral.CrystallineCupNaturality.pullback p k X Y g j y) := by
  apply (CrystallineCup.Integral.equivalence p k X hX (i + j)).injective
  apply Subtype.ext
  funext n
  rw [CrystallineCup.Integral.equivalence_coordinate, CrystallineCup.Integral.equivalence_coordinate,
    restriction_pullback, CrystallineCup.Integral.restriction_cup, CrystallineCup.Integral.restriction_cup,
    restriction_pullback, restriction_pullback]
  exact WittGeometricCup.cup_natural p k X Y g n i j
    (CrystallineCup.Integral.restriction p k Y n i x) (CrystallineCup.Integral.restriction p k Y n j y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupNaturality.Integral
