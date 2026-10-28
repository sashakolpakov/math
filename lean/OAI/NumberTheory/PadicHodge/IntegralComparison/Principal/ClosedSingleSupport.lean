import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedSurvivor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.TerminalScalars

/-! # Closed Single Support -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSingleSupport

noncomputable section

/-! The original globally supported survivor has its canonical lift
to the additive principal Čech diagram. No point value is reselected. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SingleAdditiveSections
variable {Z X : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
  (N : Z.Modules) (S : X.Modules) (e : S ≅ (Scheme.Modules.pushforward f).obj N)
  (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)
  (hW : ∀ i, SectionPresheaf.openSubset U (W i) ≤ SectionIdealPuncturedCover.outside f.ker)
  (c : ℕ)

include N e hW in
theorem intersection_zero (p q : ℕ) (hq : 0 < q) (a : AugmentedOrdered.Cech.Index ι q) :
    IsZero (((SingleAdditiveSections.sheafDiagram U hU S c).X p).obj
      (op ((AugmentedOrdered.Cech.formal W q).obj a))) := by
  let V := SectionPresheaf.openSubset U ((AugmentedOrdered.Cech.formal W q).obj a)
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  change IsZero (E.obj ((SingleAdditiveSections.sheafSingle S c).X p))
  by_cases hp : p = c
  · subst p
    have hz : IsZero (E.obj (Closed.SupportedSurvivor.sheaf S)) :=
      (AdditiveSections.forgetScalars U).map_isZero
        (SupportedSurvivor.intersection_zero f N S e U hU W hW q hq a)
    exact hz.of_iso (E.mapIso (singleObjXSelf (.up ℕ) c (Closed.SupportedSurvivor.sheaf S)))
  · exact E.map_isZero (isZero_single_obj_X (.up ℕ) c (Closed.SupportedSurvivor.sheaf S) p hp)

abbrev terminalOpen := (AdditiveSections.opens U hU).obj (⊤_ SectionPresheaf.Index U)
abbrev outside := SectionIdealPuncturedCover.outside f.ker

def toPrincipal := Closed.SupportedSurvivor.lift f N S e (terminalOpen U hU) c ≫
  SupportedOrderedCechEdge.Abelian.map AddCommGrpCat.{u} X (AdditiveSections.opens U hU) W (outside f)
    (SingleAdditiveSections.sheafSingle S c) hW

abbrev forget_normalization :=
  SupportedOrderedCechForget.Abelian.global_lift_forget AddCommGrpCat.{u} X
    (AdditiveSections.opens U hU) W (outside f) (SingleAdditiveSections.sheafSingle S c) hW
      (Closed.SupportedSurvivor.terms_zero f N S e c)

abbrev normalization :=
  SupportedOrderedCechForget.Abelian.global_lift_factorization AddCommGrpCat.{u} X
    (AdditiveSections.opens U hU) W (outside f) (SingleAdditiveSections.sheafSingle S c) hW
      (intersection_zero f N S e U hU W hW c)
      (Closed.SupportedSurvivor.terms_zero f N S e c)

abbrev homology_normalization :=
  OrderedCechForgetHomology.AbelianSupported.global_lift_homology AddCommGrpCat.{u} X
    (AdditiveSections.opens U hU) W (outside f) (SingleAdditiveSections.sheafSingle S c) hW
      (intersection_zero f N S e U hU W hW c)
      (Closed.SupportedSurvivor.terms_zero f N S e c)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSingleSupport
