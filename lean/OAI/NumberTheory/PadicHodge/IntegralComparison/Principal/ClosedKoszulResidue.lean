import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedQuotient

/-! # Closed Koszul Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedKoszulResidue

noncomputable section

/-! The oriented normal-Koszul residue lands in the original closed
structure sheaf on the complete principal-open diagram. Its coefficient
map is the literal original scheme pullback of functions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U) {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)

abbrev target := SectionPresheaf.modules U hU (ClosedQuotient.directImage f)

def pullback : KoszulPartial.Fractions.modules Γ(Y, U) (SectionPresheaf.rings U hU) ⟶ target f U hU :=
  Koszul.QuotientCoefficientPresheaf.moduleMk Γ(Y, U) (SectionPresheaf.rings U hU) s ≫
    (ClosedQuotient.iso f U hU s hs).hom

theorem pullback_apply (r : (SectionPresheaf.Index U)ᵒᵖ) (a : Γ(Y, SectionPresheaf.openSubset U r.unop)) :
    (pullback f U hU s hs).app r a = f.app (SectionPresheaf.openSubset U r.unop) a :=
  ClosedQuotient.component_mk f U hU s hs r.unop a

include hs in
theorem annihilated (r : (SectionPresheaf.Index U)ᵒᵖ) (i : Fin c) (x : (target f U hU).obj r) : s i • x = 0 := by
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((ClosedQuotient.iso f U hU s hs).hom.app r)).surjective x
  rw [← ((ClosedQuotient.iso f U hU s hs).hom.app r).hom.map_smul,
    Koszul.QuotientCoefficientPresheaf.annihilated, map_zero]

def residue : KoszulPartial.Components.coefficient Γ(Y, U) (SectionPresheaf.rings U hU) s ⟶
    (single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(Y, U)) (.up ℕ) c).obj (target f U hU) :=
  Koszul.CoefficientResidue.complexMap Γ(Y, U) (SectionPresheaf.rings U hU) s (target f U hU)
    (pullback f U hU s hs) (annihilated f U hU s hs)

theorem evaluation (r : (SectionPresheaf.Index U)ᵒᵖ)
    (φ : (⋀[Γ(Y, U)]^c (Fin c → Γ(Y, U))) →ₗ[Γ(Y, U)] Γ(Y, SectionPresheaf.openSubset U r.unop)) :
    (Koszul.CoefficientResidue.evaluation Γ(Y, U) (SectionPresheaf.rings U hU) s (target f U hU)
      (pullback f U hU s hs)).app r φ =
      f.app (SectionPresheaf.openSubset U r.unop) (φ (TopExteriorCoordinates.generator (Pi.basisFun Γ(Y, U) (Fin c)))) :=
  pullback_apply f U hU s hs r _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedKoszulResidue
