import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientFrames

/-! # Coefficient Hyperplane -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientHyperplane

noncomputable section

/-! Use the native IntegralModel coefficient base-change isomorphisms for the
actual hyperplane sheaf and its tensor powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientFrames.PolarizationEmbedding
attribute [local instance 2000] MvPolynomial.gradedAlgebra

variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}

theorem coefficient_hyperplane_iso_of_coordinates
    (p : Proj (homogeneousSubmodule (Fin (n + 1)) K) ⟶
      Proj (homogeneousSubmodule (Fin (n + 1)) R))
    (hO : ∀ i : Fin (n + 1), p ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i)
    (hR : ∀ i k : Fin (n + 1), p.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i)
      (hO i).ge (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) =
        SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := K) i k)
    (j : Fin (n + 1)) :
    Nonempty ((Scheme.Modules.pullback p).obj (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≅
      SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := K) j) :=
  RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing.exists_iso_of_equal_frame_transitions
    (X := Proj (homogeneousSubmodule (Fin (n + 1)) K)) (ι := Fin (n + 1))
    ((Scheme.Modules.pullback p).obj (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j))
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := K) j)
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K)) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := K))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K)) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K))
    (fun i k => (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq (R := K) i k).ge)
    (IntegralModel.Projective.CoefficientFrames.PolarizationEmbedding.coefficientHyperplaneFrame p hO j) (IntegralModel.Projective.CoefficientFrames.PolarizationEmbedding.nativeBaseChangeFrame (K := K) j)
    (IntegralModel.Projective.CoefficientFrames.PolarizationEmbedding.coefficientOverlapRatio (K := K))
    (IntegralModel.Projective.CoefficientFrames.PolarizationEmbedding.coefficientHyperplaneFrame_overlap p hO hR j) (IntegralModel.Projective.CoefficientFrames.PolarizationEmbedding.nativeHyperplaneFrame_overlap (K := K) j)

variable (φ : R →+* K) (n : ℕ)

theorem coefficient_hyperplane_iso (j : Fin (n + 1)) :
    Nonempty ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≅ SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := K) j) :=
  coefficient_hyperplane_iso_of_coordinates (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)
    (IntegralModel.Projective.CoefficientRatios.PolarizationEmbedding.coefficientCoordinateOpen_preimage φ) (IntegralModel.Projective.CoefficientRatios.PolarizationEmbedding.coefficientCoordinateRatio_section φ) j

theorem coefficient_hyperplane_power_iso (j : Fin (n + 1)) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) ≅
        SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j m) := by
  obtain ⟨e⟩ := IntegralModel.HyperplanePullbackPowers.PolarizationEmbedding.hyperplane_pullback_power_iso
    (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)
    (IntegralModel.Projective.HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine K n j) j (coefficient_hyperplane_iso φ n j) m
  exact ⟨e ≪≫ (IntegralModel.IntrinsicProjectivePowers.PolarizationEmbedding.nativeHyperplanePowerIso K n j m).symm⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientHyperplane
