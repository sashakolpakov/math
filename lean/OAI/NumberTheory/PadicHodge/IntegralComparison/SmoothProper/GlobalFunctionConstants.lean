import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.EtaleSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFactor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline

/-! # Global Function Constants -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionConstants

noncomputable section

/-! Witt vectors of actual global functions give classes in the original integral and rational crystalline degree-zero cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Finite k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "W" => WittVector p k
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

def sections (w : WittVector p A) : Crystalline.ConstantSections.Sections
    (p := p) (J := Ideal.span {(p : W)}) («δ» := δ) f := by
  let := GlobalFunctionWitt.etale p k X hprojective
  exact Crystalline.EtaleSections.sectionOf (WittVector p A)
    (GlobalFunction.WittFactor.factor k X p) (GlobalFunction.WittFactor.overBase k X p) w

theorem value_reduction (w : WittVector p A)
    (U : BigCrystallineSite.Object p W (Ideal.span {(p : W)}) δ f) :
    Ideal.Quotient.mk U.ideal (Crystalline.ConstantSections.value f (sections p k X hprojective w) U) =
      Crystalline.EtaleResidue.residueRingMap (WittVector p A)
        (GlobalFunction.WittFactor.factor k X p) U w := by
  let := GlobalFunctionWitt.etale p k X hprojective
  change Ideal.Quotient.mk U.ideal (Crystalline.ConstantSections.value f
    (Crystalline.EtaleSections.sectionOf (WittVector p A)
      (GlobalFunction.WittFactor.factor k X p) (GlobalFunction.WittFactor.overBase k X p) w) U) = _
  rw [Crystalline.EtaleSections.value_sectionOf]
  exact Crystalline.EtaleLift.reduction_apply _ _ _ U w

def bigMap : WittVector p A →ₗ[W] BigCrystallineCohomology.Cohomology
    (p := p) (J := Ideal.span {(p : W)}) («δ» := δ) f 0 := by
  let := GlobalFunctionWitt.etale p k X hprojective
  exact Crystalline.EtaleSections.baseCohomologyMap (WittVector p A)
    (GlobalFunction.WittFactor.factor k X p) (GlobalFunction.WittFactor.overBase k X p)

theorem bigMap_sections (w : WittVector p A) :
    Crystalline.ConstantSections.cohomologyEquiv f (bigMap p k X hprojective w) =
      sections p k X hprojective w := by
  let := GlobalFunctionWitt.etale p k X hprojective
  exact (Crystalline.ConstantSections.cohomologyEquiv f).apply_symm_apply _

def integralMap : WittVector p A →ₗ[W] Witt.Crystalline.integralCohomology p k X 0 :=
  (Global.Crystalline.Comparison.integralEquivWitt p k X 0).toLinearMap.comp (bigMap p k X hprojective)

def rationalMap : TensorProduct W (FractionRing W) (WittVector p A) →ₗ[FractionRing W]
    Witt.Crystalline.rationalCohomology p k X 0 :=
  (integralMap p k X hprojective).baseChange (FractionRing W)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionConstants
