import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates

/-! # Intrinsic Projective Embedding -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicProjectiveEmbedding.GradedHilbert

noncomputable section

/-! An affine native Hilbert family has an actual closed embedding in
polynomial projective space, with its canonical homogeneous ideal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {R : Type u} [CommRing R] (n : ℕ)
variable (a : Spec (CommRingCat.of R) ⟶ S)
variable (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))

def affineNativeProjectiveEmbedding : F.val.subscheme ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  F.val.subschemeι ≫ (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).inv

instance affineNativeProjectiveEmbedding_closed : IsClosedImmersion (affineNativeProjectiveEmbedding n a F) :=
  inferInstanceAs (IsClosedImmersion (F.val.subschemeι ≫ (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).inv))

theorem affineNativeProjectiveEmbedding_projection :
    affineNativeProjectiveEmbedding n a F ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) =
      Hilbert.Functor.familyProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) F.val := by
  rw [affineNativeProjectiveEmbedding, Category.assoc, ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_inv_projection]
  rfl

theorem affineNativeProjectiveEmbedding_ambient :
    affineNativeProjectiveEmbedding n a F ≫ Projective.Point.GradedHilbert.projectiveSchemePointMap n a =
      F.val.subschemeι ≫ (prod.snd : Over.mk a ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left := by
  rw [← ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projective, affineNativeProjectiveEmbedding, Category.assoc,
    Iso.inv_hom_id_assoc]

theorem affineNativeProjectiveEmbedding_coordinates :
    ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (affineNativeProjectiveEmbedding n a F).ker = IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F := by
  have h : (affineNativeProjectiveEmbedding n a F).ker = F.val.comap (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom :=
    (Global.PolynomialInclusion.closedImmersion_comp_iso_ker F.val.subschemeι (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).symm).trans
      (congrArg (fun J => J.comap (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom) F.val.ker_subschemeι)
  exact congrArg ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicProjectiveEmbedding.GradedHilbert
