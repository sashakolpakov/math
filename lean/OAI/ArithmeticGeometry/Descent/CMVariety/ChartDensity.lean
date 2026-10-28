import OAI.ArithmeticGeometry.Descent.CMVariety.AffineCoordinates
import OAI.ArithmeticGeometry.Descent.CMVariety.BaseChangeMaps

/-! # Chart Density -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ChartDensity.Abelian

noncomputable section

/-! Number-field points are dense in every rational chart with a smooth,
quasi-finite coordinate map. The factorization is an equality of scheme maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def IsNumberFieldPoint {X : Scheme} (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) : Prop :=
  ∃ (K : Subfield ℂ), NumberField K ∧ ∃ pK : Spec (CommRingCat.of K) ⟶ X,
    Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p

abbrev arithmeticPointProjection {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ))
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase f)) : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X :=
  s.left ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))

theorem arithmetic_chart_numberField_points_dense
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ))
    (n : ℕ) (u : X ⟶ (AffineCoordinates.Abelian.rationalAffineSpace (Fin n)).left)
    (hu : u ≫ (AffineCoordinates.Abelian.rationalAffineSpace (Fin n)).hom = f)
    [Smooth u] [LocallyQuasiFinite u] :
    Dense {s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase f) |
      IsNumberFieldPoint (arithmeticPointProjection f s)} := by
  let q := (AffineCoordinates.Abelian.rationalAffineSpace (Fin n)).hom
  have : Algebra.Smooth ℚ (MvPolynomial (Fin n) ℚ) := ⟨inferInstance, inferInstance⟩
  have : Smooth q := (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr (inferInstanceAs (Algebra.Smooth ℚ (MvPolynomial (Fin n) ℚ))))
  let v := BaseChangeMaps.Abelian.arithmeticBaseChangeMap f q u hu
  have hd := (AffineCoordinates.Abelian.rationalAffineSpace_closed_arithmetic_points_dense (Fin n)).preimage
    (BaseChangeMaps.Abelian.arithmeticBaseChangeMap_isOpenMap f q u hu)
  apply hd.mono
  intro s hs
  apply QuasiFinitePoints.Abelian.complex_point_descends_of_quasiFinite_closed_coordinates u q
    (arithmeticPointProjection f s)
  have he : arithmeticPointProjection q (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v s) =
      arithmeticPointProjection f s ≫ u := by
    change (s.left ≫ v.left) ≫ _ = (s.left ≫ _) ≫ u
    rw [Category.assoc, BaseChangeMaps.Abelian.arithmeticBaseChangeMap_fst, ← Category.assoc]
  change IsClosed {(arithmeticPointProjection q (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v s))
    (IsLocalRing.closedPoint ℂ)} at hs
  rwa [he] at hs

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ChartDensity.Abelian
