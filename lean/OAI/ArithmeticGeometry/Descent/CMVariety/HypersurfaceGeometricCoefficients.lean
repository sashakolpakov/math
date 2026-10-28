import OAI.ArithmeticGeometry.Descent.CMVariety.GeometricAffineCoefficients
import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceChartBaseChange
import OAI.ArithmeticGeometry.Descent.CMVariety.HypersurfaceSpread
import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceCoefficients

/-! # Hypersurface Geometric Coefficients -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.HypersurfaceGeometricCoefficients.Abelian

noncomputable section

/-! Geometrically integral coefficient models for the monic hypersurface
charts supplied by Noether normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

theorem monic_hypersurface_chart_has_geometric_model
    (R K : Type) [CommRing R] [Field K] [IsAlgClosed K] [Algebra R K]
    (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) K)) (hp : p.Monic)
    (hdegree : 0 < p.natDegree) (d : MvPolynomial (Fin n) K) (hd : d ≠ 0)
    (hirr : Irreducible (MvPolynomial.map (algebraMap K K)
      ((MvPolynomial.finSuccEquiv K n).symm p))) :
    ∃ M : AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models.Coefficients.CoefficientModel R K (Models.SpreadingOut.Affine.Construction.affineOver K
      (Localization.Away (algebraMap (MvPolynomial (Fin n) K) (AdjoinRoot p) d))),
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  obtain ⟨s, p₀, d₀, hmap, hdmap, hmonic, hdeg⟩ :=
    Models.SpreadingOut.HypersurfaceCoefficients.Construction.monic_hypersurface_coefficients_descend R K n p hp d
  let S := Models.CoefficientSystem.Constructions.Foundations.coefficientRing R K s
  have hd₀ : d₀ ≠ 0 := by
    intro h
    apply hd
    rw [← hdmap, h, map_zero]
  have hdeg₀ : 0 < p₀.natDegree := hdeg ▸ hdegree
  have hirr₀ : Irreducible (MvPolynomial.map (algebraMap S K)
      ((MvPolynomial.finSuccEquiv S n).symm p₀)) := by
    have he : MvPolynomial.map (algebraMap S K)
        ((MvPolynomial.finSuccEquiv S n).symm p₀) =
        MvPolynomial.map (algebraMap K K)
          ((MvPolynomial.finSuccEquiv K n).symm p) := by
      rw [IsScalarTower.algebraMap_eq S K K, ← MvPolynomial.map_map,
        Models.SpreadingOut.PolynomialCoordinates.Construction.map_finSuccEquiv_symm, hmap]
    exact he ▸ hirr
  let C := Localization.Away (algebraMap (MvPolynomial (Fin n) S) (AdjoinRoot p₀) d₀)
  have : Algebra.FinitePresentation S (AdjoinRoot p₀) := inferInstance
  have : Algebra.FinitePresentation S C :=
    Algebra.FinitePresentation.trans S (AdjoinRoot p₀) C
  obtain ⟨r, hr, hgood⟩ := HypersurfaceSpread.Abelian.localized_hypersurface_domain_after_inverting_base_element
    S K Subtype.val_injective n p₀ hmonic hdeg₀ d₀ hd₀ hirr₀
  obtain ⟨M, hconn, hirred⟩ := GeometricAffineCoefficients.Abelian.coefficient_model_of_eventually_integral_affine R K s C r hr hgood
  obtain ⟨e⟩ := Models.SpreadingOut.HypersurfaceChartBaseChange.Construction.hypersurface_chart_generic_iso_of_coefficients S K n p₀ d₀ p d hmap hdmap
  exact ⟨M.transport (Models.SpreadingOut.Affine.Construction.affineOverIso e), hconn, hirred⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.HypersurfaceGeometricCoefficients.Abelian
