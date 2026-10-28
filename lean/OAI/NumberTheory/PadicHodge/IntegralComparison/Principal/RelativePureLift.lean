import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeSupportedClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.SupportedPureClass

/-! # Relative Pure Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativePureLift

noncomputable section

/-! The original principal supported localization is exactly the
canonical relative pure-complex lift, with no change to its global coefficient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativeConcentration
variable {X Z : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)
  (f : Z ⟶ X) [IsClosedImmersion f] (N : Z.Modules)
  (e : K.homology c ≅ (Scheme.Modules.pushforward f).obj N)
  (hW : ∀ i, SectionPresheaf.openSubset U (W i) ≤ SectionIdealPuncturedCover.outside f.ker)

include hW in
theorem comparison_lift (q : ℕ) :
    PrincipalReference.SupportedClass.Reference.localize U hU W K c hK f N e hW q ≫
      (RelativeConcentration.comparison U hU W K q).hom =
    Relative.SupportedPureClass.lift (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
      (RelativeConcentration.family U hU W) (RelativeConcentration.family_affine U hU W) K c hK f N e hW q := by
  apply (cancel_mono
    (Relative.SupportedPureClass.survivorIso (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
      (RelativeConcentration.family U hU W) (RelativeConcentration.family_affine U hU W) K c hK q).hom).mp
  have h := RelativeSupportedClass.localize_relative U hU W K c hK f N e hW q
  have hn := Relative.SupportedPureClass.normalization (RelativeConcentration.ambient U hU) (RelativeConcentration.ambient_affine U hU)
    (RelativeConcentration.family U hU W) (RelativeConcentration.family_affine U hU W) K c hK f N e hW q
  exact (Category.assoc _ _ _).symm.trans (h.trans hn.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.RelativePureLift
