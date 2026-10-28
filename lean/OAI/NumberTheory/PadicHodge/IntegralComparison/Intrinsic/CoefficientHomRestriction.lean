import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.IntrinsicCoefficientHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomPrincipalExt

/-! # Coefficient Hom Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CoefficientHomRestriction

noncomputable section

/-! Native finite-projective coefficient purity, valued in the actual
internal Hom into one fixed scalar dualizing sheaf, respects principal
restriction. No scalar purity frames are used on either open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation
open OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.IntrinsicCoefficientHom

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (K L : ChainComplex X.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  [∀ q, ((Affine.LinearResolutionPurity.internalComplex N L).X q).IsQuasicoherent]
  (M M' : X.Modules) [M.IsQuasicoherent] [M'.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  (ε' : L ⟶ (ChainComplex.single₀ X.Modules).obj M') [QuasiIso ε']
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  (Q : Type u) [CommRing Q] [Algebra Γ(X, U) Q]
  (hQ : Function.Surjective (algebraMap Γ(X, U) Q))
  (C : Type u) [AddCommGroup C] [Module Q C] [Module Γ(X, U) C]
  [IsScalarTower Γ(X, U) Q C] [Module.Finite Q C] [Module.Projective Q C]
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) Q)
  (eC : (AffineOpen.InternalHom.sections U hU).obj M' ≅ ModuleCat.of Γ(X, U) C)
  (n : ℕ)
  (V : X.Modules) [Module Q Γ(V, U)] [IsScalarTower Γ(X, U) Q Γ(V, U)]
  (κ : (Affine.LinearResolutionPurity.internalComplex N K).homology n ≅ V)

variable (r : Γ(X, U))
  [∀ q, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  [∀ q, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj (K.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj (L.X q))]
  (Q' : Type u) [CommRing Q'] [Algebra Γ(X, AffinePrincipal.Sections.openSubset U r) Q']
  (hQ' : Function.Surjective (algebraMap Γ(X, AffinePrincipal.Sections.openSubset U r) Q'))
  (C' : Type u) [AddCommGroup C'] [Module Q' C'] [Module Γ(X, AffinePrincipal.Sections.openSubset U r) C']
  [IsScalarTower Γ(X, AffinePrincipal.Sections.openSubset U r) Q' C'] [Module.Finite Q' C'] [Module.Projective Q' C']
  (eM' : (AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj M ≅
    ModuleCat.of Γ(X, AffinePrincipal.Sections.openSubset U r) Q')
  (eC' : (AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj M' ≅
    ModuleCat.of Γ(X, AffinePrincipal.Sections.openSubset U r) C')
  [Module Q' Γ(V, AffinePrincipal.Sections.openSubset U r)] [IsScalarTower Γ(X, AffinePrincipal.Sections.openSubset U r) Q' Γ(V, AffinePrincipal.Sections.openSubset U r)]
  (hmul : ∀ (q : Q) (m : C),
    Affine.CoefficientRestriction.coefficientRestriction U hU M' C eC r C' eC' (q • m) =
      Affine.CoefficientRestriction.scalarRestriction U hU M Q eM r Q' eM' q •
        Affine.CoefficientRestriction.coefficientRestriction U hU M' C eC r C' eC' m)
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

include hmul eN in
theorem restriction (z : Γ((Affine.LinearResolutionPurity.internalComplex N L).homology n, U)) :
    (Affine.IntrinsicCoefficientHom.iso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) N K L M M' ε ε' Q' hQ' C' eM' eC' n V κ).hom
        (((Affine.LinearResolutionPurity.internalComplex N L).homology n).presheaf.map
          (AffinePrincipal.Sections.inclusion U r).op z) =
      (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M' V).presheaf.map (AffinePrincipal.Sections.inclusion U r).op
        ((Affine.IntrinsicCoefficientHom.iso U hU N K L M M' ε ε' Q hQ C eM eC n V κ).hom z) := by
  apply Affine.HomPrincipalExt.ext U hU r M' V
  intro m
  rw [Affine.IntrinsicCoefficientHom.evaluation, Affine.HomEvaluation.restriction,
    Affine.IntrinsicCoefficientHom.evaluation]
  have hm : Affine.CoefficientRestriction.coefficientRestriction U hU M' C eC r C' eC'
      (Affine.IntrinsicCoefficientHom.coefficientIso U hU M' C eC m) =
      Affine.IntrinsicCoefficientHom.coefficientIso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) M' C' eC'
        (M'.presheaf.map (AffinePrincipal.Sections.inclusion U r).op m) := by
    change eC'.hom ((Affine.ChartSections.iso (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) M').hom
      (M'.presheaf.map (AffinePrincipal.Sections.inclusion U r).op ((Affine.ChartSections.iso U hU M').inv
        (eC.inv (eC.hom ((Affine.ChartSections.iso U hU M').hom m)))))) = _
    rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]
    rfl
  have hp := Affine.CoefficientRestriction.restriction U hU N K L M M' ε ε' Q C eM eC
    r Q' C' eM' eC' hmul eN n z (Affine.IntrinsicCoefficientHom.coefficientIso U hU M' C eC m)
  rw [hm] at hp
  rw [← hp]
  exact PresheafOfModules.naturality_apply κ.hom.val (AffinePrincipal.Sections.inclusion U r).op _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CoefficientHomRestriction
