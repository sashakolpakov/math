import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientRatios
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackPowers
import OAI.RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing

/-! # Coefficient Frames -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientFrames

/-! The native projective hyperplane sheaf and all its powers commute with
coefficient extension. The isomorphism is glued from the actual coordinate
ratios, so it applies to the standard field coordinates in Presentations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

namespace PolarizationEmbedding

attribute [local instance 2000] MvPolynomial.gradedAlgebra
variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}
  (p : Proj (homogeneousSubmodule (Fin (n + 1)) K) ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R))
  (hO : ∀ i : Fin (n + 1), p ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i)
  (hR : ∀ i k : Fin (n + 1), p.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i)
    (hO i).ge (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) = SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := K) i k)

def coefficientOverlapRatio (i k : Fin (n + 1)) :
    Γ(Proj (homogeneousSubmodule (Fin (n + 1)) K), SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k) :=
  SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := K) i k

include hR in
theorem coefficientCoordinateRatio_overlap (i k : Fin (n + 1)) :
    p.appLE
      (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k)
      ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i k).trans (hO i).ge)
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) =
        (coefficientOverlapRatio (K := K) i k :
          Γ(Proj (homogeneousSubmodule (Fin (n + 1)) K), SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k)) := by
  have h := congrArg ((Proj (homogeneousSubmodule (Fin (n + 1)) K)).presheaf.map
    (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i k)).op)
      (hR i k)
  have hm := ConcreteCategory.congr_hom
    (p.appLE_map
      (hO i).ge
      (homOfLE (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i k)).op)
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k)
  exact hm.symm.trans h

def coefficientHyperplaneFrame (j i : Fin (n + 1)) :
    ((Scheme.Modules.pullback p).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)).restrict (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i).ι ≅
        SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i).toScheme :=
  SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hO i).ge
    (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame p j i)

theorem coefficientHyperplaneFrame_restrict (j i : Fin (n + 1))
    (U : (Proj (homogeneousSubmodule (Fin (n + 1)) K)).Opens) (h : U ≤ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i) :
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization h (coefficientHyperplaneFrame p hO j i) =
      SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (h.trans (hO i).ge)
        (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame p j i) :=
  SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp (hO i).ge h _

include hR in
theorem coefficientRawHyperplane_overlap (j i k : Fin (n + 1)) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
      ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i k).trans (hO i).ge)
      (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame p j i)).hom =
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
      ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K) i k).trans (hO k).ge)
      (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame p j k)).hom ≫
        SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k).topIso.inv
          (coefficientOverlapRatio (K := K) i k)) := by
  have he := FrameRatios.PolarizationEmbedding.hyperplanePullbackFrame_transition_on
    p j i k (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k)
    ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i k).trans (hO i).ge)
    ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K) i k).trans (hO k).ge)
  exact he.trans (congrArg
    (fun a : Γ(Proj (homogeneousSubmodule (Fin (n + 1)) K), SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k) =>
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
        ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K) i k).trans (hO k).ge)
        (HyperplanePullbackFrames.PolarizationEmbedding.hyperplanePullbackFrame p j k)).hom ≫
          SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k).topIso.inv a))
      (coefficientCoordinateRatio_overlap p hO hR i k))

include hR in
theorem coefficientHyperplaneFrame_overlap (j i k : Fin (n + 1)) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i k)
      (coefficientHyperplaneFrame p hO j i)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K) i k)
        (coefficientHyperplaneFrame p hO j k)).hom ≫
          SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k).topIso.inv
            (coefficientOverlapRatio (K := K) i k)) := by
  have hl := congrArg Iso.hom (coefficientHyperplaneFrame_restrict p hO j i _
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i k))
  have hr := congrArg Iso.hom (coefficientHyperplaneFrame_restrict p hO j k _
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K) i k))
  exact hl.trans ((coefficientRawHyperplane_overlap p hO hR j i k).trans
    (congrArg (fun h => h ≫ SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
      ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k).topIso.inv (coefficientOverlapRatio (K := K) i k))) hr.symm))

def nativeBaseChangeFrame (j i : Fin (n + 1)) :
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := K) j).restrict (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i).ι ≅
      SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i).toScheme :=
  SheafCohomology.Projective.HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := K) i j

theorem nativeHyperplaneFrame_overlap (j i k : Fin (n + 1)) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K) i k)
      (nativeBaseChangeFrame (K := K) j i)).hom =
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K) i k)
        (nativeBaseChangeFrame (K := K) j k)).hom ≫
          SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K) i k).topIso.inv
            (coefficientOverlapRatio (K := K) i k)) :=
  SheafCohomology.Projective.HyperplaneFrameTransition.MvPolynomial.coordinateHyperplanePole_frameTransition (R := K) i k j

end PolarizationEmbedding

end AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientFrames

namespace AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientFrames.PolarizationEmbedding

/-! Native projective hyperplane powers commute with coefficient extension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

-- Match the native coordinate sheaves when instantiating generic module gluing.
attribute [local instance 2000] MvPolynomial.gradedAlgebra
variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}

variable (p : Proj (homogeneousSubmodule (Fin (n + 1)) K) ⟶
  Proj (homogeneousSubmodule (Fin (n + 1)) R))
  (hO : ∀ i : Fin (n + 1), p ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i)
  (hR : ∀ i k : Fin (n + 1), p.appLE (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i)
    (hO i).ge (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i k) = SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := K) i k)

include hR in
theorem hyperplane_pullback_iso_of_coordinates (j : Fin (n + 1)) :
    Nonempty ((Scheme.Modules.pullback p).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≅ SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := K) j) :=
  RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing.exists_iso_of_equal_frame_transitions
    (X := Proj (homogeneousSubmodule (Fin (n + 1)) K)) (ι := Fin (n + 1))
    ((Scheme.Modules.pullback p).obj (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j))
    (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := K) j)
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K)) (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := K))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := K))
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := K)) (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := K))
    (fun i k => (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq (R := K) i k).ge)
    (coefficientHyperplaneFrame p hO j) (nativeBaseChangeFrame (K := K) j)
    (coefficientOverlapRatio (K := K))
    (coefficientHyperplaneFrame_overlap p hO hR j) (nativeHyperplaneFrame_overlap (K := K) j)

variable (φ : R →+* K)

theorem coefficientHyperplane_pullback_iso (j : Fin (n + 1)) :
    Nonempty ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)).obj
      (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≅ SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := K) j) :=
  hyperplane_pullback_iso_of_coordinates (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)
    (CoefficientRatios.PolarizationEmbedding.coefficientCoordinateOpen_preimage φ) (CoefficientRatios.PolarizationEmbedding.coefficientCoordinateRatio_section φ) j

theorem coefficientHyperplane_powers_iso (j : Fin (n + 1)) (m : ℕ) :
    Nonempty ((Scheme.Modules.pullback (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m) ≅
        SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j m) := by
  obtain ⟨e⟩ := HyperplanePullbackPowers.PolarizationEmbedding.hyperplane_pullback_power_iso (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)
    (HyperplanePowers.PolarizationEmbedding.projectiveHyperplaneLine K n j) j (coefficientHyperplane_pullback_iso φ j) m
  exact ⟨e ≪≫ (IntrinsicProjectivePowers.PolarizationEmbedding.nativeHyperplanePowerIso K n j m).symm⟩

end AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientFrames.PolarizationEmbedding

end

end OAI
