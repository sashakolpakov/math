import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.HomEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientScalarRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientTarget

/-! # Closed Internal Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom

noncomputable section

/-! Internal Hom on the ambient principal diagram is the Hom diagram
over the actual closed-scheme section ring, with literal coefficient evaluation. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X Z : Scheme.{u}} (i : X ⟶ Z) [IsClosedImmersion i]
  (U : Z.Opens) (hU : IsAffineOpen U) (M N : X.Modules) [M.IsQuasicoherent]
private abbrev ambientRing := Γ(Z, U)
private abbrev closedRing := Γ(X, i ⁻¹ᵁ U)
private abbrev sourceModule := ModuleCat.of (closedRing i U) Γ(M, i ⁻¹ᵁ U)
private abbrev scalarRestriction := ModuleCat.restrictScalars (i.app U).hom
private abbrev image (L : X.Modules) := (Scheme.Modules.pushforward i).obj L
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom.ambientRing U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom.closedRing i U
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom.sourceModule i U M
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom.scalarRestriction i U
local notation "PM" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom.image i M
local notation "PN" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom.image i N
local instance closedAlgebra : Algebra A Q := (i.app U).hom.toAlgebra
local instance source_qc : (PM).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i

def sourceIso : (G).obj B ≅ ModuleCat.of A Γ(PM, U) :=
  (show (G).obj B ≃ₗ[A] Γ(PM, U) from
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toModuleIso

def iso : SectionPresheaf.modules U hU (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule PM PN) ≅
    HomCoefficientFunctor.homPresheaf Q (ClosedScalars.modules i U hU N) B ⋙ G :=
  InternalHom.iso U hU PM PN ≪≫
    (HomCoefficientFunctor.functor A (SectionPresheaf.modules U hU PN)).mapIso (sourceIso i U M).op ≪≫
    HomCoefficientTarget.iso A ((G).obj B) (ClosedScalars.restrictionIso i U hU N).symm ≪≫
    (HomCoefficientScalarRestriction.iso A Q (i.app_surjective U hU)
      (ClosedScalars.modules i U hU N) B).symm

theorem hom_apply (r : (SectionPresheaf.Index U)ᵒᵖ)
    (φ : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule PM PN, SectionPresheaf.openSubset U r.unop))
    (x : Γ(M, i ⁻¹ᵁ U)) :
    (show Γ(M, i ⁻¹ᵁ U) →ₗ[Q] Γ(N, i ⁻¹ᵁ SectionPresheaf.openSubset U r.unop) from
      (iso i U hU M N).hom.app r φ) x =
    Affine.HomEvaluation.evaluation PM PN (SectionPresheaf.openSubset U r.unop) φ
      ((PM).presheaf.map (SectionPresheaf.inclusion U r.unop).op x) := by
  change (show Γ(PM, U) →ₗ[A] Γ(PN, SectionPresheaf.openSubset U r.unop) from
    (InternalHom.iso U hU PM PN).hom.app r φ) x = _
  exact InternalHom.hom_apply U hU PM PN r φ x

theorem evaluation (x : Γ(M, i ⁻¹ᵁ U)) :
    (iso i U hU M N).hom ≫
      Functor.whiskerRight (HomPresheafDualFrame.evaluation Q
        (ClosedScalars.modules i U hU N) B x) G ≫
      (ClosedScalars.restrictionIso i U hU N).hom =
    HomEvaluation.map U hU PM PN x := by
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  exact hom_apply i U hU M N r φ x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedInternalHom
