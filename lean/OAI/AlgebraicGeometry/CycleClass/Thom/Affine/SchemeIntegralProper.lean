import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.AffineCompactness
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! # Scheme Integral Proper -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeIntegralProper.Constructions

noncomputable section

/-! An actual integral map of affine complex schemes is proper in the
ordinary analytic topology when the target is locally of finite type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem isProperMap_affine_integral {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    [IsIntegralHom f.left] [LocallyOfFiniteType Y.hom] :
    IsProperMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  let A := Γ(Y.left, ⊤)
  let B := Γ(X.left, ⊤)
  let φ := ComplexPoints.Analytic.AffineSchemePointTopology.affineCoordinateHom f
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have hi : IsIntegralHom (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    have h := congrArg Over.Hom.left (Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_over f)
    simp only [Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv_left, Over.comp_left,
      Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso_inv_left, Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso_hom_left] at h
    let : IsClosedImmersion X.left.isoSpec.inv := inferInstance
    let : IsClosedImmersion Y.left.isoSpec.hom := inferInstance
    have hj : IsIntegralHom (X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom) := inferInstance
    exact h.symm ▸ hj
  let : Algebra.IsIntegral A B := ⟨IsIntegralHom.SpecMap_iff.mp hi⟩
  let : Algebra.FiniteType ℂ A := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType Y
  have hp : IsProperMap (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap φ) :=
    Thom.Integral.AffineCompactness.Constructions.isProperMap_character_comap A B
  rw [ComplexPoints.Analytic.AffineSchemePointTopology.schemePointMap_eq_affineCoordinates]
  exact (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph Y).symm.isProperMap.comp
    (hp.comp (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X).isProperMap)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeIntegralProper.Constructions
