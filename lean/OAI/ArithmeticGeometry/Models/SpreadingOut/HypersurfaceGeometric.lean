import OAI.ArithmeticGeometry.Models.SpreadingOut.AffineGeometric
import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceChartBaseChange
import OAI.ArithmeticGeometry.Models.SpreadingOut.Hypersurface
import OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceCoefficients

/-! # Hypersurface Geometric -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceGeometric.Construction

noncomputable section

/-! Geometrically integral coefficient models for the monic hypersurface
charts supplied by Noether normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct _root_.NumberField

universe u

theorem monic_hypersurface_chart_has_geometric_model
    (K : Type u) [Field K] [NumberField K]
    (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) K)) (hp : p.Monic)
    (hdegree : 0 < p.natDegree) (d : MvPolynomial (Fin n) K) (hd : d ≠ 0)
    (hirr : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
      ((MvPolynomial.finSuccEquiv K n).symm p))) :
    ∃ M : Foundations.Constructions.CoefficientModel K (Affine.Construction.affineOver K
      (Localization.Away (algebraMap (MvPolynomial (Fin n) K) (AdjoinRoot p) d))),
      GeometricallyConnected M.model.hom ∧ GeometricallyIrreducible M.model.hom := by
  obtain ⟨s, p₀, d₀, hmap, hdmap, hmonic, hdeg⟩ :=
    HypersurfaceCoefficients.Construction.monic_hypersurface_coefficients_descend (𝓞 K) K n p hp d
  let S := CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s
  have : IsFractionRing S K := CoefficientFractionRing.Construction.subalgebra_fractionRing (𝓞 K) K S
  have hd₀ : d₀ ≠ 0 := by
    intro h
    apply hd
    rw [← hdmap, h, map_zero]
  have hdeg₀ : 0 < p₀.natDegree := hdeg ▸ hdegree
  have hirr₀ : Irreducible (MvPolynomial.map (algebraMap S (AlgebraicClosure K))
      ((MvPolynomial.finSuccEquiv S n).symm p₀)) := by
    have he : MvPolynomial.map (algebraMap S (AlgebraicClosure K))
        ((MvPolynomial.finSuccEquiv S n).symm p₀) =
        MvPolynomial.map (algebraMap K (AlgebraicClosure K))
          ((MvPolynomial.finSuccEquiv K n).symm p) := by
      rw [IsScalarTower.algebraMap_eq S K (AlgebraicClosure K), ← MvPolynomial.map_map,
        PolynomialCoordinates.Construction.map_finSuccEquiv_symm, hmap]
    exact he ▸ hirr
  let C := Localization.Away (algebraMap (MvPolynomial (Fin n) S) (AdjoinRoot p₀) d₀)
  have : Algebra.FinitePresentation S (AdjoinRoot p₀) := inferInstance
  have : Algebra.FinitePresentation S C :=
    Algebra.FinitePresentation.trans S (AdjoinRoot p₀) C
  obtain ⟨r, hr, hgood⟩ := Hypersurface.Construction.localized_hypersurface_domain_after_inverting_base_element
    S K n p₀ hmonic hdeg₀ d₀ hd₀ hirr₀
  obtain ⟨M, hconn, hirred⟩ := AffineGeometric.Construction.coefficient_model_of_eventually_integral_affine K s C r hr hgood
  obtain ⟨e⟩ := HypersurfaceChartBaseChange.Construction.hypersurface_chart_generic_iso_of_coefficients S K n p₀ d₀ p d hmap hdmap
  exact ⟨M.transport (Affine.Construction.affineOverIso e), hconn, hirred⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceGeometric.Construction
