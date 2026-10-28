import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Concentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSingleSupport

/-! # Supported Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SupportedClass.Reference

noncomputable section

/-! Localize an original global survivor class through the canonical
supported edge and the original sheaf concentration maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → Principal.SectionPresheaf.Index U)
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

def concentratedIso (q : ℕ) :=
  (Principal.AdditiveSections.forgetScalars U).mapIso (Concentration.Reference.iso U hU W K c hK q) ≪≫
    Principal.SingleAdditiveSections.homologyIso U hU (K.homology c) c W q

variable {Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f]
  (N : Z.Modules) (e : K.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hW : ∀ i, Principal.SectionPresheaf.openSubset U (W i) ≤ SectionIdealPuncturedCover.outside f.ker)

def localize (q : ℕ) :=
  homologyMap (Principal.ClosedSingleSupport.toPrincipal f N (K.homology c) e U hU W hW c) q ≫
    (concentratedIso U hU W K c hK q).inv

@[reassoc]
theorem localize_concentrated (q : ℕ) : localize U hU W K c hK f N e hW q ≫
    (concentratedIso U hU W K c hK q).hom =
      homologyMap (Principal.ClosedSingleSupport.toPrincipal f N (K.homology c) e U hU W hW c) q := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (concentratedIso U hU W K c hK q).inv_hom_id).trans (Category.comp_id _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.SupportedClass.Reference
