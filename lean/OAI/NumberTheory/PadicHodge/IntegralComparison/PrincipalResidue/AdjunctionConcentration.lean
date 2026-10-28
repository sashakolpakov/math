import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.Adjunction

/-! # Adjunction Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AdjunctionConcentration

noncomputable section

/-! The original residue total, followed by its differential symbol,
is the original sheaf concentration followed by the actual adjunction. -/

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
  (M : X.Modules) [M.IsQuasicoherent] (ω : Γ(M, f ⁻¹ᵁ U))
  (φ : (Affine.LinearResolutionPurity.internalComplex N K).homology c ⟶
    (Scheme.Modules.pushforward f).obj M)
  (hlocal : (Affine.ModuleExactSections.sections U).map φ =
    SurvivorSection.sectionMap U hU N e K f ε s hs hreg ≫
      Principal.PushforwardSectionCoordinates.sectionsMap f U M ω)

variable {ι : Type u} [LinearOrder ι] (W : ι → Principal.SectionPresheaf.Index U)
  (hD : ∀ q, q ≠ c → (Affine.LinearResolutionPurity.internalComplex N K).ExactAt q)

include hlocal in
theorem comparison (q : ℕ) :
    (Supported.CechHomotopyEquivalence.functor W q).map
      (Principal.OrientedResidue.map f U hU N e K ε s hs hreg) ≫
        (Supported.CechHomotopyEquivalence.functor W q).map
          ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U)) (.up ℕ) c).map
            (Principal.PushforwardSection.map f U hU M ω)) =
    (PrincipalReference.Concentration.Reference.iso U hU W
      (Affine.LinearResolutionPurity.internalComplex N K) c hD q).hom ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((singleMapHomologicalComplex (Principal.ModuleFunctor.functor U hU)
          (.up ℕ) c).hom.app ((Affine.LinearResolutionPurity.internalComplex N K).homology c)) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U)) (.up ℕ) c).map
          ((Principal.ModuleFunctor.functor U hU).map φ)) := by
  rw [Principal.OrientedResidueConcentration.map U hU N e K f ε s hs hreg W hD q]
  rw [Adjunction.comparison U hU N e K f ε s hs hreg M ω φ hlocal]
  simp only [Functor.map_comp, Category.assoc]

include hlocal in
theorem original_map (q : ℕ) :
    (Supported.CechHomotopyEquivalence.functor W q).map
      (Principal.OrientedResidue.map f U hU N e K ε s hs hreg) ≫
        (Supported.CechHomotopyEquivalence.functor W q).map
          ((single ((Principal.SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U)) (.up ℕ) c).map
            (Principal.PushforwardSection.map f U hU M ω)) =
    (PrincipalReference.Concentration.Reference.iso U hU W
      (Affine.LinearResolutionPurity.internalComplex N K) c hD q).hom ≫
      (PrincipalReference.Concentration.Reference.functor U hU W q).map
        ((single Y.Modules (.up ℕ) c).map φ) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((singleMapHomologicalComplex (Principal.ModuleFunctor.functor U hU)
          (.up ℕ) c).hom.app ((Scheme.Modules.pushforward f).obj M)) := by
  rw [comparison U hU N e K f ε s hs hreg M ω φ hlocal W hD q]
  have h := congrArg (fun b => (Supported.CechHomotopyEquivalence.functor W q).map b)
    ((singleMapHomologicalComplex (Principal.ModuleFunctor.functor U hU)
      (.up ℕ) c).hom.naturality φ)
  simp only [Functor.comp_map, Functor.map_comp] at h
  rw [← h]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.AdjunctionConcentration
