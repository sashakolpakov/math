import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorSection
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PushforwardSectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionTransformationAtOne
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalQuasiIso

/-! # Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.Adjunction

noncomputable section

/-! An actual sheaf adjunction with the original affine residue
coordinate agrees with that residue on the whole principal diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose {C : Type*} [Category C] {A B D E F G : C}
    (u : A ⟶ B) (v : F ⟶ G) (w : D ⟶ E)
    (x : B ⟶ E) (y : E ⟶ G) (z : B ⟶ G)
    (a : A ⟶ D) (b : D ⟶ F) (q : A ⟶ F)
    (hnat : u ≫ z = q ≫ v) (hq : q = a ≫ b)
    (hu : u ≫ x = a ≫ w) (hv : w ≫ y = b ≫ v) :
    u ≫ z = u ≫ (x ≫ y) := by
  calc
    _ = q ≫ v := hnat
    _ = (a ≫ b) ≫ v := congrArg (fun t => t ≫ v) hq
    _ = a ≫ (w ≫ y) := (Category.assoc _ _ _).trans (congrArg (fun t => a ≫ t) hv.symm)
    _ = (u ≫ x) ≫ y := (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ y) hu.symm)
    _ = _ := Category.assoc _ _ _

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
  (M : X.Modules) [M.IsQuasicoherent] (ω : Γ(M, f ⁻¹ᵁ U))
  (φ : (Affine.LinearResolutionPurity.internalComplex N K).homology c ⟶
    (Scheme.Modules.pushforward f).obj M)
  (hlocal : (Affine.ModuleExactSections.sections U).map φ =
    SurvivorSection.sectionMap U hU N e K f ε s hs hreg ≫
      Principal.PushforwardSectionCoordinates.sectionsMap f U M ω)

include hlocal in
theorem comparison :
    (Principal.ModuleFunctor.functor U hU).map φ =
      SurvivorData.map U hU N e K f ε s hs hreg ≫
        Principal.PushforwardSection.map f U hU M ω := by
  let := Affine.LocalQuasiIso.homology_quasicoherent
    (Affine.LinearResolutionPurity.internalComplex N K) c
  let : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  apply Principal.SectionTransformationAtOne.Ext.ext_atOne U hU _ _
  apply (cancel_epi ((Principal.AtOne.iso U hU).app
    ((Affine.LinearResolutionPurity.internalComplex N K).homology c)).hom).mp
  exact compose _ _ _ _ _ _ _ _ _
    ((Principal.AtOne.iso U hU).hom.naturality φ).symm hlocal
    (SurvivorSection.atOne U hU N e K f ε s hs hreg)
    (Principal.PushforwardSectionCoordinates.atOne_hom f U hU M ω)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.Adjunction
