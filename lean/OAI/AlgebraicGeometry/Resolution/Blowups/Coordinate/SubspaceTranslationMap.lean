import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceTranslation
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealChartDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.ComplexAffineDifferentialIdeal
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Subspace Translation Map -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceTranslationMap.Construction

noncomputable section

/-! Coordinate translations are actual étale maps of the complex affine model and preserve its marked coordinate ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def coordinateSubspaceTranslationMap {σ τ : Type} (a : τ → ℂ) :
    Spec (.of (MvPolynomial (σ ⊕ τ) ℂ)) ⟶ Spec (.of (MvPolynomial (σ ⊕ τ) ℂ)) :=
  Spec.map (CommRingCat.ofHom (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ => 0) a)).toRingHom)

instance coordinateSubspaceTranslationMap_etale {σ τ : Type} (a : τ → ℂ) :
    Etale (coordinateSubspaceTranslationMap (σ := σ) a) :=
  (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom
    (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ : σ => 0) a)).toRingHom)).mpr
      (RingHom.Etale.of_bijective (PolynomialTranslation.Construction.polynomialTranslationEquiv (Sum.elim (fun _ : σ => 0) a)).bijective)

theorem coordinateSubspaceTranslationMap_ground {σ τ : Type} (a : τ → ℂ) :
    coordinateSubspaceTranslationMap (σ := σ) a ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (σ ⊕ τ) ℂ) =
      ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (MvPolynomial (σ ⊕ τ) ℂ) := by
  rw [coordinateSubspaceTranslationMap, ComplexAffineDifferentialIdeal.Construction.complexSpecStructure, ← Spec.map_comp]
  congr 1
  have h : (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ : σ => 0) a)).toRingHom.comp
      (algebraMap ℂ (MvPolynomial (σ ⊕ τ) ℂ)) = algebraMap ℂ (MvPolynomial (σ ⊕ τ) ℂ) := by
    apply RingHom.ext
    intro r
    exact (PolynomialTranslation.Construction.polynomialTranslate (Sum.elim (fun _ : σ => 0) a)).commutes r
  exact congrArg CommRingCat.ofHom h

theorem coordinateSubspaceTranslationMap_ideal {σ τ : Type} (a : τ → ℂ) :
    (Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker (SubspaceIdeal.Construction.polynomialCoordinateProjection (σ := σ) (τ := τ) (R := ℂ)).toRingHom)).comap
      (coordinateSubspaceTranslationMap a) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (RingHom.ker SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom) := by
  rw [coordinateSubspaceTranslationMap, Affine.IdealChartDescent.Construction.affineQuotientKernel_comap_hom,
    SubspaceTranslation.Construction.polynomialCoordinateProjection_ker_map_translation]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SubspaceTranslationMap.Construction
