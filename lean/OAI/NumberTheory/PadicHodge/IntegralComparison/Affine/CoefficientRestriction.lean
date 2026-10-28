import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.CoefficientMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientEvaluationBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.OrientedPurity

/-! # Coefficient Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientRestriction

noncomputable section

/-! Coefficient evaluation on native dual cohomology sheaves commutes
with literal principal-open restriction. This statement precedes any
choice of scalar purity coordinate or target differential-form frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent]
  (K L : ChainComplex X.Modules ℕ)
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (L.X q).IsQuasicoherent]
  [∀ q, ((LinearResolutionPurity.internalComplex N K).X q).IsQuasicoherent]
  [∀ q, ((LinearResolutionPurity.internalComplex N L).X q).IsQuasicoherent]
  (M M' : X.Modules) [M.IsQuasicoherent] [M'.IsQuasicoherent]
  (ε : K ⟶ (ChainComplex.single₀ X.Modules).obj M) [QuasiIso ε]
  (ε' : L ⟶ (ChainComplex.single₀ X.Modules).obj M') [QuasiIso ε']
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  (Q : Type u) [CommRing Q] [Algebra Γ(X, U) Q]
  (C : Type u) [AddCommGroup C] [Module Q C] [Module Γ(X, U) C]
  [IsScalarTower Γ(X, U) Q C]
  (eM : (AffineOpen.InternalHom.sections U hU).obj M ≅ ModuleCat.of Γ(X, U) Q)
  (eC : (AffineOpen.InternalHom.sections U hU).obj M' ≅ ModuleCat.of Γ(X, U) C)

def pullback (n : ℕ)
    (z : Γ((LinearResolutionPurity.internalComplex N L).homology n, U))
    (m : C) : Γ((LinearResolutionPurity.internalComplex N K).homology n, U) :=
  (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n).inv
    (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N))
      (CoefficientLifts.resolution U hU K M ε (ModuleCat.of Γ(X, U) Q) eM)
      (CoefficientLifts.resolution U hU L M' ε' (ModuleCat.of Γ(X, U) C) eC)
      (Quotient.CoefficientEvaluation.point Γ(X, U) Q C m) n
      ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z))

omit [N.IsQuasicoherent] in
theorem comparison_pullback (n : ℕ)
    (z : Γ((LinearResolutionPurity.internalComplex N L).homology n, U)) (m : C) :
    (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n).hom
        (pullback U hU N K L M M' ε ε' Q C eM eC n z m) =
      Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj N))
        (CoefficientLifts.resolution U hU K M ε (ModuleCat.of Γ(X, U) Q) eM)
        (CoefficientLifts.resolution U hU L M' ε' (ModuleCat.of Γ(X, U) C) eC)
        (Quotient.CoefficientEvaluation.point Γ(X, U) Q C m) n
        ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z) :=
  ConcreteCategory.congr_hom (AffinePrincipal.Cohomology.Comparison.comparison U hU N K n).inv_hom_id _

variable (r : Γ(X, U))
  [∀ q, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X q))]
  [∀ q, Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  [∀ q, Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (L.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj (K.X q))]
  [∀ q, Projective ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj (L.X q))]
  (Q' : Type u) [CommRing Q'] [Algebra Γ(X, AffinePrincipal.Sections.openSubset U r) Q']
  (C' : Type u) [AddCommGroup C'] [Module Q' C'] [Module Γ(X, AffinePrincipal.Sections.openSubset U r) C']
  [IsScalarTower Γ(X, AffinePrincipal.Sections.openSubset U r) Q' C']
  (eM' : (AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj M ≅
    ModuleCat.of Γ(X, AffinePrincipal.Sections.openSubset U r) Q')
  (eC' : (AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj M' ≅
    ModuleCat.of Γ(X, AffinePrincipal.Sections.openSubset U r) C')

abbrev scalarRestriction := AffinePrincipal.CoefficientMaps.restriction U hU r M
  (ModuleCat.of Γ(X, U) Q) (ModuleCat.of Γ(X, AffinePrincipal.Sections.openSubset U r) Q') eM eM'

abbrev coefficientRestriction := AffinePrincipal.CoefficientMaps.restriction U hU r M'
  (ModuleCat.of Γ(X, U) C) (ModuleCat.of Γ(X, AffinePrincipal.Sections.openSubset U r) C') eC eC'

variable (hmul : ∀ (q : Q) (m : C),
  coefficientRestriction U hU M' C eC r C' eC' (q • m) =
    scalarRestriction U hU M Q eM r Q' eM' q •
      coefficientRestriction U hU M' C eC r C' eC' m)
  (eN : (AffineOpen.InternalHom.sections U hU).obj N ≅ ModuleCat.of Γ(X, U) Γ(X, U))

include hmul eN in
theorem restriction (n : ℕ)
    (z : Γ((LinearResolutionPurity.internalComplex N L).homology n, U)) (m : C) :
    ((LinearResolutionPurity.internalComplex N K).homology n).presheaf.map
        (AffinePrincipal.Sections.inclusion U r).op (pullback U hU N K L M M' ε ε' Q C eM eC n z m) =
      pullback (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) N K L M M' ε ε' Q' C' eM' eC' n
        (((LinearResolutionPurity.internalComplex N L).homology n).presheaf.map
          (AffinePrincipal.Sections.inclusion U r).op z)
        (coefficientRestriction U hU M' C eC r C' eC' m) := by
  let : IsLocalization.Away r Γ(X, AffinePrincipal.Sections.openSubset U r) := hU.isLocalization_basicOpen r
  let : Module.Flat Γ(X, U) Γ(X, AffinePrincipal.Sections.openSubset U r) :=
    IsLocalization.flat Γ(X, AffinePrincipal.Sections.openSubset U r) (Submonoid.powers r)
  let P := CoefficientLifts.resolution U hU K M ε (ModuleCat.of Γ(X, U) Q) eM
  let PC := CoefficientLifts.resolution U hU L M' ε' (ModuleCat.of Γ(X, U) C) eC
  let P' := CoefficientLifts.resolution (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) K M ε
    (ModuleCat.of Γ(X, AffinePrincipal.Sections.openSubset U r) Q') eM'
  let PC' := CoefficientLifts.resolution (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) L M' ε'
    (ModuleCat.of Γ(X, AffinePrincipal.Sections.openSubset U r) C') eC'
  let (q : ℕ) : Module.Free Γ(X, U) (P.complex.X q) :=
    inferInstanceAs (Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X q)))
  let (q : ℕ) : Module.Finite Γ(X, U) (P.complex.X q) :=
    inferInstanceAs (Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (K.X q)))
  let (q : ℕ) : Module.Free Γ(X, U) (PC.complex.X q) :=
    inferInstanceAs (Module.Free Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (L.X q)))
  let (q : ℕ) : Module.Finite Γ(X, U) (PC.complex.X q) :=
    inferInstanceAs (Module.Finite Γ(X, U) ((AffineOpen.InternalHom.sections U hU).obj (L.X q)))
  have hp := CoefficientEvaluationBaseChange.pullback Γ(X, U) Γ(X, AffinePrincipal.Sections.openSubset U r) Q Q' C C'
    (AffinePrincipal.CoefficientMaps.tensorMap U hU r M _ _ eM eM')
    (AffinePrincipal.CoefficientMaps.tensorMap U hU r M' _ _ eC eC')
    (scalarRestriction U hU M Q eM r Q' eM')
    (coefficientRestriction U hU M' C eC r C' eC')
    (AffinePrincipal.CoefficientMaps.tensorMap_tmul U hU r M _ _ eM eM')
    (AffinePrincipal.CoefficientMaps.tensorMap_tmul U hU r M' _ _ eC eC') hmul
    P PC P' PC'
    (AffinePrincipal.PrincipalComplex.chartIso U hU r (.down ℕ) K)
    (AffinePrincipal.PrincipalComplex.chartIso U hU r (.down ℕ) L)
    (AffinePrincipal.CoefficientMaps.augmentation U hU r M _ _ eM eM' K ε)
    (AffinePrincipal.CoefficientMaps.augmentation U hU r M' _ _ eC eC' L ε')
    ((AffineOpen.InternalHom.sections U hU).obj N) ((AffineOpen.InternalHom.sections (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r)).obj N)
    eN (AffinePrincipal.LinearHom.targetFrame U hU r N eN) n
    ((AffinePrincipal.Cohomology.Comparison.comparison U hU N L n).hom z) m
  have hK := AffinePrincipal.OrientedPurity.comparison_restriction U hU r N K eN
    (pullback U hU N K L M M' ε ε' Q C eM eC n z m)
  have hL := AffinePrincipal.OrientedPurity.comparison_restriction U hU r N L eN z
  rw [comparison_pullback] at hK
  apply (ConcreteCategory.bijective_of_isIso
    (AffinePrincipal.Cohomology.Comparison.comparison (AffinePrincipal.Sections.openSubset U r) (hU.basicOpen r) N K n).hom).injective
  rw [comparison_pullback, ← hK, ← hL]
  exact hp.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.CoefficientRestriction
