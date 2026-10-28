import OAI.ArithmeticGeometry.Descent.CMVariety.AffineCoefficientObjects
import OAI.ArithmeticGeometry.Descent.CMVariety.ComplexParameter
import OAI.ArithmeticGeometry.Descent.CMVariety.DenseAlgebraicCoordinates
import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicCoordinatePoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Affine Coordinates -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AffineCoordinates.Abelian

noncomputable section

/-! Native complex coordinates on rational affine space and the density
of points whose rational scheme images are closed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

abbrev rationalAffineSpace (ι : Type) : Over (Spec (CommRingCat.of ℚ)) :=
  AffineCoefficientObjects.Abelian.affineCoefficientObject ℚ (MvPolynomial ι ℚ)

def rationalAffineSpaceComplexIso (ι : Type) :
    ComplexParameter.Abelian.arithmeticComplexBase (rationalAffineSpace ι).hom ≅
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (MvPolynomial ι ℂ) :=
  AffineCoefficientObjects.Abelian.affineCoefficientBaseChangeIso ℚ ℂ (MvPolynomial ι ℚ) ≪≫
    AffineCoefficientObjects.Abelian.affineCoefficientAlgIso (MvPolynomial.algebraTensorAlgEquiv ℚ ℂ)

def rationalAffineCoordinates (ι : Type) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase (rationalAffineSpace ι).hom) ≃ₜ (ι → ℂ) :=
  ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (rationalAffineSpaceComplexIso ι)).trans
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph (MvPolynomial ι ℂ)).symm).trans
      (AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation.polynomialPointHomeomorph ι)

theorem rationalAffineSpaceComplexIso_projection (ι : Type) :
    (rationalAffineSpaceComplexIso ι).hom.left ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap ℚ ℂ))) =
    pullback.fst (rationalAffineSpace ι).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := ι) ℚ ℂ
  have h : e.symm.toRingHom.comp (MvPolynomial.map (algebraMap ℚ ℂ)) =
      (Algebra.TensorProduct.includeRight :
        MvPolynomial ι ℚ →ₐ[ℚ] ℂ ⊗[ℚ] MvPolynomial ι ℚ).toRingHom := by
    apply RingHom.ext
    intro p
    exact MvPolynomial.algebraTensorAlgEquiv_symm_map ℚ ℂ p
  change ((pullbackSymmetry _ _).hom ≫ (pullbackSpecIso ℚ ℂ (MvPolynomial ι ℚ)).hom ≫
    Spec.map (CommRingCat.ofHom e.symm.toRingHom)) ≫ _ = _
  erw [Category.assoc, Category.assoc, ← Spec.map_comp]
  change (pullbackSymmetry _ _).hom ≫ (pullbackSpecIso ℚ ℂ (MvPolynomial ι ℚ)).hom ≫
    Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (MvPolynomial.map (algebraMap ℚ ℂ)))) = _
  erw [h, pullbackSpecIso_hom_snd, pullbackSymmetry_hom_comp_snd]
  rfl

theorem rationalAffineCoordinates_projection (ι : Type)
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase (rationalAffineSpace ι).hom)) :
    s.left ≫ pullback.fst (rationalAffineSpace ι).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) =
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := ℚ) (rationalAffineCoordinates ι s)).toRingHom) := by
  let e := rationalAffineSpaceComplexIso ι
  let x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ) :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (MvPolynomial ι ℂ)).symm (s ≫ e.hom)
  have hs : Spec.map (CommRingCat.ofHom x.toRingHom) = s.left ≫ e.hom.left := by
    have h := congrArg (fun t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (MvPolynomial ι ℂ)) => t.left)
      ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (MvPolynomial ι ℂ)).apply_symm_apply (s ≫ e.hom))
    exact (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left _ x).symm.trans h
  have heval : x.toRingHom.comp (MvPolynomial.map (algebraMap ℚ ℂ)) =
      (MvPolynomial.aeval (R := ℚ) (rationalAffineCoordinates ι s)).toRingHom := by
    apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_X]
      rfl
  rw [← rationalAffineSpaceComplexIso_projection ι]
  erw [← Category.assoc, ← hs, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom heval)

theorem rationalAffineSpace_closed_arithmetic_points_dense (ι : Type) :
    Dense {s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase (rationalAffineSpace ι).hom) |
      IsClosed {(s.left ≫ pullback.fst (rationalAffineSpace ι).hom
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))) (IsLocalRing.closedPoint ℂ)}} := by
  have h := (DenseAlgebraicCoordinates.Abelian.algebraic_coordinate_tuples_dense ι).preimage
    (rationalAffineCoordinates ι).isOpenMap
  apply h.mono
  intro s hs
  change IsClosed {_}
  rw [rationalAffineCoordinates_projection]
  exact AlgebraicCoordinatePoints.Abelian.algebraic_polynomial_evaluation_closed _ hs

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AffineCoordinates.Abelian
