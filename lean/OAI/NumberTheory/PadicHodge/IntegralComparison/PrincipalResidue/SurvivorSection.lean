import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorCoordinates

/-! # Survivor Section -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorSection

noncomputable section

/-! The original residue on the surviving sheaf, expressed directly
as a section of the closed structure sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ k, (K.X k).IsQuasicoherent]
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (Principal.ClosedQuotient.directImage f))
  [QuasiIso ε] [∀ k, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X k))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  [∀ k, ((Affine.LinearResolutionPurity.internalComplex N K).X k).IsQuasicoherent]

attribute [local instance] Principal.OrientedResidue.structure_quasicoherent

def coefficientIso : (Affine.ModuleExactSections.sections U).obj
    (Principal.ClosedQuotient.directImage f) ≅
      ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s) :=
  Affine.ChartSections.iso U hU (Principal.ClosedQuotient.directImage f) ≪≫
    Principal.OrientedResidue.quotientIso f U hU s hs

def sectionMap : (Affine.ModuleExactSections.sections U).obj
    ((Affine.LinearResolutionPurity.internalComplex N K).homology c) ⟶
      (Affine.ModuleExactSections.sections U).obj (Principal.ClosedQuotient.directImage f) :=
  (Affine.OrientedPurity.iso U hU N K (Principal.ClosedQuotient.directImage f) ε
    (KoszulPartial.Resolution.normalIdeal Γ(Y, U) s)
    (Principal.OrientedResidue.quotientIso f U hU s hs) s rfl hreg
    (Principal.OrientedResidueNormalizationBase.lineIso U hU N e)).hom ≫
      (coefficientIso U hU f s hs).inv

theorem atOne :
    ((Principal.AtOne.iso U hU).app
      ((Affine.LinearResolutionPurity.internalComplex N K).homology c)).hom ≫
      (SurvivorData.map U hU N e K f ε s hs hreg).app (op (Principal.AtOne.object U)) =
    sectionMap U hU N e K f ε s hs hreg ≫
      ((Principal.AtOne.iso U hU).app (Principal.ClosedQuotient.directImage f)).hom := by
  apply (cancel_mono (Principal.OrientedResidueNormalization.targetAtOne U hU f s hs).hom).mp
  calc
    _ = SurvivorData.normalized U hU N e K f ε s hs hreg := Category.assoc _ _ _
    _ = _ := SurvivorCoordinates.comparison U hU N e K f ε s hs hreg
    _ = _ := by
      simp only [sectionMap, coefficientIso, Principal.OrientedResidueNormalization.targetAtOne,
        Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorSection
