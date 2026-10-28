import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.QuotientCoefficientPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.QuotientSectionNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.IdealSheafPrincipalEquations

/-! # Closed Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedQuotient

noncomputable section

/-! The normal-equation quotient presheaf on the original principal
opens is the literal structure sheaf direct image of the closed scheme.
The comparison sends each residue class to the original pullback. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U) {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)

abbrev coefficient := KoszulPartial.Fractions.modules Γ(Y, U)
  (Koszul.QuotientCoefficientPresheaf.quotient Γ(Y, U) (SectionPresheaf.rings U hU) s)
abbrev directImage := Closed.QuotientSectionNormalization.directImage f

include hs in
omit [IsClosedImmersion f] in
theorem ideal_eq (r : SectionPresheaf.Index U) :
    Koszul.QuotientCoefficientPresheaf.ideal Γ(Y, U) (SectionPresheaf.rings U hU) s (op r) =
      Closed.QuotientSectionNormalization.ideal f (SectionPresheaf.openSubset U r) (hU.basicOpen r.val) :=
  IdealSheafPrincipalEquations.generates f.ker U hU r.val s hs

local instance sectionTower (r : SectionPresheaf.Index U) :
    IsScalarTower Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U r) Γ(directImage f, SectionPresheaf.openSubset U r) where
  smul_assoc a b m := by
    change (algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U r) a * b) • m =
      algebraMap Γ(Y, U) Γ(Y, SectionPresheaf.openSubset U r) a • (b • m)
    exact mul_smul _ _ _

def component (r : SectionPresheaf.Index U) : (coefficient U hU s).obj (op r) ≃ₗ[Γ(Y, U)]
    Γ(directImage f, SectionPresheaf.openSubset U r) := by
  let I : Ideal Γ(Y, SectionPresheaf.openSubset U r) :=
    Koszul.QuotientCoefficientPresheaf.ideal Γ(Y, U) (SectionPresheaf.rings U hU) s (op r)
  let J : Ideal Γ(Y, SectionPresheaf.openSubset U r) :=
    Closed.QuotientSectionNormalization.ideal f (SectionPresheaf.openSubset U r) (hU.basicOpen r.val)
  have h : I = J := ideal_eq f U hU s hs r
  let q : (Γ(Y, SectionPresheaf.openSubset U r) ⧸ I) ≃ₗ[Γ(Y, SectionPresheaf.openSubset U r)] Γ(directImage f, SectionPresheaf.openSubset U r) :=
    ((Ideal.quotientEquivAlgOfEq Γ(Y, SectionPresheaf.openSubset U r) h).toLinearEquiv).trans
      (Closed.QuotientSectionNormalization.iso f (SectionPresheaf.openSubset U r) (hU.basicOpen r.val)).symm.toLinearEquiv
  exact q.restrictScalars Γ(Y, U)

theorem component_mk (r : SectionPresheaf.Index U) (a : Γ(Y, SectionPresheaf.openSubset U r)) :
    component f U hU s hs r (Ideal.Quotient.mk _ a) = f.app (SectionPresheaf.openSubset U r) a := by
  let I : Ideal Γ(Y, SectionPresheaf.openSubset U r) :=
    Koszul.QuotientCoefficientPresheaf.ideal Γ(Y, U) (SectionPresheaf.rings U hU) s (op r)
  let J : Ideal Γ(Y, SectionPresheaf.openSubset U r) :=
    Closed.QuotientSectionNormalization.ideal f (SectionPresheaf.openSubset U r) (hU.basicOpen r.val)
  have h : I = J := ideal_eq f U hU s hs r
  change (Closed.QuotientSectionNormalization.iso f (SectionPresheaf.openSubset U r) (hU.basicOpen r.val)).inv
    ((Ideal.quotientEquivAlgOfEq Γ(Y, SectionPresheaf.openSubset U r) h) (Ideal.Quotient.mk I a)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Closed.QuotientSectionNormalization.iso_inv_mk f (SectionPresheaf.openSubset U r) (hU.basicOpen r.val) a

def iso : coefficient U hU s ≅ SectionPresheaf.modules U hU (directImage f) :=
  NatIso.ofComponents (fun r => (component f U hU s hs r.unop).toModuleIso) (by
    intro r t a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Γ(Y, SectionPresheaf.openSubset U r.unop) ⧸
      Koszul.QuotientCoefficientPresheaf.ideal Γ(Y, U) (SectionPresheaf.rings U hU) s r at x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change component f U hU s hs t.unop
        (Ideal.Quotient.mk _ (Y.presheaf.map (SectionPresheaf.arrow U hU a.unop).op x)) =
      (directImage f).presheaf.map (SectionPresheaf.arrow U hU a.unop).op
        (component f U hU s hs r.unop (Ideal.Quotient.mk _ x))
    rw [component_mk, component_mk]
    exact ConcreteCategory.congr_hom (f.naturality (SectionPresheaf.arrow U hU a.unop).op) x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedQuotient
