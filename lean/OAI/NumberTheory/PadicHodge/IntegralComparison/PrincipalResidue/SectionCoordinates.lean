import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorSection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.OrientedPurityTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LineFrameNormalization

/-! # Section Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SectionCoordinates.Survivor

noncomputable section

/-! The section coefficient of the genuine principal residue uses
the original closed quotient and the prescribed affine line frame. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Affine.OrientedPurity.iso

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (K : ChainComplex Y.Modules ℕ) [∀ k, (K.X k).IsQuasicoherent]
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (Principal.ClosedQuotient.directImage f))
  [QuasiIso ε] [∀ k, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X k))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  [∀ k, ((Affine.LinearResolutionPurity.internalComplex N K).X k).IsQuasicoherent]
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(Y, U) Γ(Y, U))

attribute [local instance] Principal.OrientedResidue.structure_quasicoherent

omit [N.IsQuasicoherent] in
theorem sectionMap_frame :
    SurvivorSection.sectionMap U hU N (Affine.LineFrameNormalization.PrincipalOrientedResidue.sectionFrame U hU N eN)
      K f ε s hs hreg =
    (Affine.OrientedPurity.iso U hU N K (Principal.ClosedQuotient.directImage f) ε
      (f.ker.ideal ⟨U, hU⟩) (Closed.QuotientSectionNormalization.chartIso f U hU)
      s hs hreg eN).hom ≫ (Closed.QuotientSectionNormalization.iso f U hU).inv := by
  have h := Affine.OrientedPurityTransport.iso_cast U hU N K
    (Principal.ClosedQuotient.directImage f) ε (f.ker.ideal ⟨U, hU⟩)
    (KoszulPartial.Resolution.normalIdeal Γ(Y, U) s) hs.symm
    (Closed.QuotientSectionNormalization.chartIso f U hU) s hs hreg eN
  dsimp only [SurvivorSection.sectionMap]
  rw [Affine.LineFrameNormalization.PrincipalOrientedResidue.lineIso_sectionFrame]
  unfold Principal.OrientedResidue.quotientIso
  rw [h]
  simp only [SurvivorSection.coefficientIso, Principal.OrientedResidue.quotientIso,
    Closed.QuotientSectionNormalization.chartIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SectionCoordinates.Survivor
