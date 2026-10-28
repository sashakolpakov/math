import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline

/-! # Crystalline Pullback -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback

noncomputable section

/-!
# Pullback on crystalline cohomology of separated schemes

Every morphism over the residue field gives exact restriction on the big
crystalline site. The proved comparison with the small site and extension
to the Witt fraction field supply integral and rational pullback maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison
open OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable {X Y : Over (Spec (CommRingCat.of k))} (g : X ⟶ Y)

local notation "W" => WittVector p k
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

omit [CharP k p] [PerfectRing k p] in
theorem over_witt : g.left ≫ IntegralComparison.Witt.Crystalline.wittStructureMap p k Y = IntegralComparison.Witt.Crystalline.wittStructureMap p k X := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  rw [← Category.assoc, g.w]

abbrev BigCohomology (X : Over (Spec (CommRingCat.of k))) (n : ℕ) :=
  IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
    (IntegralComparison.Witt.Crystalline.wittStructureMap p k X) n

def bigPullback (n : ℕ) : BigCohomology p k Y n →ₗ[W] BigCohomology p k X n := by
  let F := IntegralComparison.BigCrystallineCohomology.pullback (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
    g.left (over_witt p k g) n
  exact
    { toFun := F
      map_add' := F.map_add
      map_smul' := fun b x => F.map_smul (ULift.up b : ULift.{u + 1} W) x }

variable [IsSeparated X.hom] [IsSeparated Y.hom]

def integralPullback (n : ℕ) : IntegralComparison.Witt.Crystalline.integralCohomology p k Y n →ₗ[W] IntegralComparison.Witt.Crystalline.integralCohomology p k X n :=
  (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n).toLinearMap.comp
    ((bigPullback p k g n).comp (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k Y n).symm.toLinearMap)

def rationalPullback (n : ℕ) : IntegralComparison.Witt.Crystalline.rationalCohomology p k Y n →ₗ[FractionRing W]
    IntegralComparison.Witt.Crystalline.rationalCohomology p k X n :=
  (integralPullback p k g n).baseChange (FractionRing W)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback
