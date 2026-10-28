import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ConcentrationSingle
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.SurvivorData
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechTopNaturality

/-! # Oriented Residue Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueConcentration

noncomputable section

/-! The original oriented residue on the supported total is the
original sheaf concentration followed by its genuine survivor map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom

variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
  (N : Y.Modules) [N.IsQuasicoherent]
  (e : Γ(N, U) ≃ₗ[Γ(Y, U)] Γ(Y, U))
  (K : ChainComplex Y.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  {X : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (ε : K ⟶ (ChainComplex.single₀ Y.Modules).obj (ClosedQuotient.directImage f))
  [QuasiIso ε] [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  {c : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(Y, U) (List.ofFn s))
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]

variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U)
  (hD : ∀ q, q ≠ c → (Affine.LinearResolutionPurity.internalComplex N K).ExactAt q)

attribute [local instance] OrientedResidue.structure_quasicoherent

theorem map (q : ℕ) :
    (Supported.CechHomotopyEquivalence.functor W q).map
      (OrientedResidue.map f U hU N e K ε s hs hreg) =
    (PrincipalReference.Concentration.Reference.iso U hU W
      (Affine.LinearResolutionPurity.internalComplex N K) c hD q).hom ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((singleMapHomologicalComplex (ModuleFunctor.functor U hU)
          (.up ℕ) c).hom.app ((Affine.LinearResolutionPurity.internalComplex N K).homology c)) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U)) (.up ℕ) c).map
          (PrincipalResidue.SurvivorData.map U hU N e K f ε s hs hreg)) :=
  ConcentrationSingle.map_to_single U hU W
    (Affine.LinearResolutionPurity.internalComplex N K) c hD
    (ClosedKoszulResidue.target f U hU)
    (OrientedResidue.map f U hU N e K ε s hs hreg) q

theorem totalMap [Fintype ι] (q : ℕ) :
    homologyMap (AugmentedOrdered.CechTopNaturality.totalMap W
      (OrientedResidue.map f U hU N e K ε s hs hreg)) q =
    (PrincipalReference.Concentration.Reference.iso U hU W
      (Affine.LinearResolutionPurity.internalComplex N K) c hD q).hom ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((singleMapHomologicalComplex (ModuleFunctor.functor U hU)
          (.up ℕ) c).hom.app ((Affine.LinearResolutionPurity.internalComplex N K).homology c)) ≫
      (Supported.CechHomotopyEquivalence.functor W q).map
        ((single ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(Y, U)) (.up ℕ) c).map
          (PrincipalResidue.SurvivorData.map U hU N e K f ε s hs hreg)) :=
  OrientedResidueConcentration.map U hU N e K f ε s hs hreg W hD q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OrientedResidueConcentration
