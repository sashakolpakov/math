import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueSurvivor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ConcentrationSingle

/-! # Coefficient Residue Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueConcentration

noncomputable section

/-! The original coefficient residue on supported cohomology factors
through the original sheaf concentration and its actual survivor map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (M : Y.Modules) [M.IsQuasicoherent]
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj M) [QuasiIso ε]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  (T : ModuleCat.{u} Γ(Y, U)) (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ T)
  (P : ProjectiveResolution T)
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  (β : ModuleCat.of Γ(Y, U)
    (Γ(Y, U) ⧸ KoszulPartial.Resolution.normalIdeal Γ(Y, U) s) ⟶ T)
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)
  (hD : ∀ q, q ≠ c → (Affine.LinearResolutionPurity.internalComplex N K).ExactAt q)

theorem concentration (q : ℕ) :
    (Supported.CechHomotopyEquivalence.functor W q).map
      (CoefficientResidueData.map U hU N e M K ε T eM P f s hs hreg β) =
    (PrincipalReference.Concentration.Reference.iso U hU W
      (Affine.LinearResolutionPurity.internalComplex N K) c hD q).hom ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((singleMapHomologicalComplex (ModuleFunctor.functor U hU)
          (.up ℕ) c).hom.app ((Affine.LinearResolutionPurity.internalComplex N K).homology c)) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U)) (.up ℕ) c).map
          (CoefficientResidueSurvivor.survivor U hU N e M K ε T eM P f s hs hreg β)) :=
  ConcentrationSingle.map_to_single U hU W
    (Affine.LinearResolutionPurity.internalComplex N K) c hD
    (ClosedKoszulResidue.target f U hU)
    (CoefficientResidueData.map U hU N e M K ε T eM P f s hs hreg β) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientResidueConcentration
