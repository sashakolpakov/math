import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtalePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleAlgebraMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SectionPullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFrobenius
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionConstants
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.CrystallineFrobenius

/-! # Crystalline Frobenius -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineFrobenius

noncomputable section

/-! The original crystalline q-Frobenius acts on actual global-function classes by their Witt-vector Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (a : ℕ) (hcard : Fintype.card k = p ^ a)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

theorem sections (w : WittVector p A) :
    Functor.whiskerLeft (BigCrystallineSite.postcompose
      (BigCrystallineFrobenius.schemeFrobenius p k X a)
      (BigCrystallineFrobenius.schemeFrobenius_over_witt p k X a hcard)).op
        (SmoothProper.GlobalFunctionConstants.sections p k X hprojective w) ≫
      (BigCrystallineCohomology.presheafTransport
        (BigCrystallineFrobenius.schemeFrobenius p k X a)
        (BigCrystallineFrobenius.schemeFrobenius_over_witt p k X a hcard)).hom =
      SmoothProper.GlobalFunctionConstants.sections p k X hprojective (WittFrobenius.witt p k X w) := by
  let := SmoothProper.GlobalFunctionWitt.etale p k X hprojective
  let g := WittFactor.factor k X p
  let hg := WittFactor.overBase k X p
  let F := BigCrystallineFrobenius.schemeFrobenius p k X a
  let hF := BigCrystallineFrobenius.schemeFrobenius_over_witt p k X a hcard
  have h₁ := Crystalline.EtalePullback.section_pullback (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (WittVector p A) g hg F hF w
  have h₂ := Crystalline.EtaleAlgebraMap.section_comp (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (WittVector p A) (WittVector p A) (WittFrobenius.witt p k X)
    (F ≫ g) g (WittFrobenius.factor p k X a hcard)
    (Crystalline.EtalePullback.overBase (WittVector p A) g hg F hF) hg w
  exact h₁.trans h₂

theorem big (w : WittVector p A) :
    BigCrystallineFrobenius.integralFrobenius p k X a hcard 0
      (SmoothProper.GlobalFunctionConstants.bigMap p k X hprojective w) =
      SmoothProper.GlobalFunctionConstants.bigMap p k X hprojective (WittFrobenius.witt p k X w) := by
  let e := Crystalline.ConstantSections.cohomologyEquiv (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f
  have h := Crystalline.SectionPullback.cohomology_pullback
    (BigCrystallineFrobenius.schemeFrobenius p k X a)
    (BigCrystallineFrobenius.schemeFrobenius_over_witt p k X a hcard)
    (SmoothProper.GlobalFunctionConstants.sections p k X hprojective w)
  exact h.trans (congrArg e.symm (sections p k X hprojective a hcard w))

theorem integral (w : WittVector p A) :
    Global.CrystallineFrobenius.integralFrobenius p k X a hcard 0
      (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w) =
      SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective (WittFrobenius.witt p k X w) := by
  have h := DFunLike.congr_fun (Global.CrystallineFrobenius.integral_intertwines p k X a hcard 0)
    (SmoothProper.GlobalFunctionConstants.bigMap p k X hprojective w)
  exact h.trans (congrArg (Global.Crystalline.Comparison.integralEquivWitt p k X 0)
    (big p k X hprojective a hcard w))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineFrobenius
