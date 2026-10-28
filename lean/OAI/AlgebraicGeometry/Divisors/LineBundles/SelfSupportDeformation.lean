import OAI.AlgebraicGeometry.Divisors.LineBundles.SelfSupportDeformationPolynomial
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization

/-! # Self Support Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SelfSupportDeformation.BundleCycles

noncomputable section

/-! The actual self-support deformation chart is the relative affine
line over its quotient coefficient ring, preserving base and parameter. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] (I : Ideal R)

def selfSupportDeformationLineIso :
    Spec (.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk I)))) ≅ AffineLine.Charts.BundleCycles.affineLine (Spec (.of (R ⧸ I))) :=
  Scheme.Spec.mapIso (SelfSupportDeformationPolynomial.BundleCycles.selfSupportDeformationPolynomialEquiv I).toRingEquiv.toCommRingCatIso.op ≪≫
    LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv (R ⧸ I)

theorem selfSupportDeformationLineIso_over :
    (selfSupportDeformationLineIso I).hom ≫ AffineLine.Charts.BundleCycles.affineLineProjection (Spec (.of (R ⧸ I))) =
      Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I)
        (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk I))))) := by
  let e := SelfSupportDeformationPolynomial.BundleCycles.selfSupportDeformationPolynomialEquiv I
  have hm : CommRingCat.ofHom (algebraMap (R ⧸ I) (Polynomial (R ⧸ I))) ≫
      e.toRingEquiv.toCommRingCatIso.hom = CommRingCat.ofHom
        (algebraMap (R ⧸ I) (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk I)))) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact e.commutes r
  change (Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫ (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv (R ⧸ I)).hom) ≫ _ = _
  rw [Category.assoc, AffineLine.Charts.BundleCycles.affineLineProjection, LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv_over]
  change Spec.map e.toRingEquiv.toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) (Polynomial (R ⧸ I)))) = _
  rw [← Spec.map_comp, hm]

theorem selfSupportDeformationPolynomialEquiv_parameter :
    SelfSupportDeformationPolynomial.BundleCycles.selfSupportDeformationPolynomialEquiv I Polynomial.X =
      Deformation.Iff.BundleCycles.deformationParameter (I.map (Ideal.Quotient.mk I)) := by
  apply Subtype.ext
  rw [SelfSupportDeformationPolynomial.BundleCycles.selfSupportDeformationPolynomialEquiv_val]
  exact Polynomial.toLaurent_X

theorem selfSupportDeformationLineIso_coordinate :
    (selfSupportDeformationLineIso I).hom.appTop (AffineLine.Space.BundleCycles.affineLineCoordinate (Spec (.of (R ⧸ I)))) =
      Affine.Specialization.BundleCycles.affineDeformationParameterSection (I.map (Ideal.Quotient.mk I)) := by
  let e := SelfSupportDeformationPolynomial.BundleCycles.selfSupportDeformationPolynomialEquiv I
  let a := e.toRingEquiv.toCommRingCatIso.hom
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality a) Polynomial.X
  change (Scheme.ΓSpecIso (.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk I))))).inv
      (e Polynomial.X) = (Spec.map a).appTop (AffineLine.Space.BundleCycles.polynomialCoordinateSection (R ⧸ I)) at h
  change (Spec.map a ≫ (LineBundles.Polynomial.AffineSpace.BundleCycles.polynomialAffineSpaceEquiv (R ⧸ I)).hom).appTop
    (AffineLine.Space.BundleCycles.affineLineCoordinate (Spec (.of (R ⧸ I)))) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineLine.Space.BundleCycles.polynomialAffineSpaceEquiv_coordinate]
  exact h.symm.trans (congrArg (Scheme.ΓSpecIso
    (.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.map (Ideal.Quotient.mk I))))).inv
      (selfSupportDeformationPolynomialEquiv_parameter I))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SelfSupportDeformation.BundleCycles
