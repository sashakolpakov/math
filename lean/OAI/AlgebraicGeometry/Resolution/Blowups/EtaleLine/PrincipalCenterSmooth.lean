import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.HorizontalDerivation
import OAI.AlgebraicGeometry.Resolution.Blowups.DualPairBlowupSmooth

/-! # Principal Center Smooth -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.PrincipalCenterSmooth.Construction

noncomputable section

/-! Smoothness of actual lifted principal curve-center blowups in étale line neighborhoods. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {H R : Type u} [CommRing k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [Algebra.Smooth k H]

attribute [local instance] HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

/-- Lifting a principal coefficient center with a unit normal derivative
gives a two-equation center whose entire actual ambient blowup is smooth. -/
theorem etaleLine_principal_center_blowup_smooth (g : H) (δ : Derivation k H H)
    (hδ : δ g = 1) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (Ideal.span {g})) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  let : Algebra.Smooth H H[X] := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth k H[X] := Algebra.Smooth.comp k H H[X]
  let : Algebra.Smooth k R := Algebra.Smooth.comp k H[X] R
  let z := algebraMap H[X] R X
  let D := Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)
  let E := HorizontalDerivation.Construction.etaleLineHorizontalDerivation k (R := R) δ
  have hDz : D z = 1 := Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := H) (V := R)
  have hDg : D (algebraMap H R g) = 0 :=
    (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).map_algebraMap g
  have hEz : E z = 0 := HorizontalDerivation.Construction.etaleLineHorizontalDerivation_coordinate k δ
  have hEg : E (algebraMap H R g) = 1 := by
    change HorizontalDerivation.Construction.etaleLineHorizontalDerivation k δ (algebraMap H R g) = 1
    rw [HorizontalDerivation.Construction.etaleLineHorizontalDerivation_coefficient, hδ, map_one]
  have hI : Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) (Ideal.span {g}) = Ideal.span {z, algebraMap H R g} := by
    rw [RetractionStep.Construction.etaleLineCenter_eq, NormalDerivation.Construction.etaleLineCoefficientMap_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_insert]
    exact sup_comm _ _
  rw [hI]
  exact DualPairBlowupSmooth.Construction.dual_pair_blowup_smooth z (algebraMap H R g) D E hDz hDg hEz hEg

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.PrincipalCenterSmooth.Construction
