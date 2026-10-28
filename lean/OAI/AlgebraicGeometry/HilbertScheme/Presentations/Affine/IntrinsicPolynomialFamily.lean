import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialInclusion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport

/-! # Intrinsic Polynomial Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicPolynomialFamily.GradedHilbert

noncomputable section

/-! Native Hilbert families on affine spectrum tests are exactly actual
flat finitely presented closed families in polynomial projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (n : ℕ) {R : Type u} [CommRing R]
variable (a : Spec (CommRingCat.of R) ⟶ S)

theorem polynomialProjectiveStructureMap_proper : IsProper (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)) :=
  Projective.Properness.GradedHilbert.projectiveStructureMap_proper (Hilbert.Polynomial.GradedHilbert.grading R n) (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.degreeZeroConstants R n).surjective

def affineNativeToPolynomial
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :
    AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))) := by
  let G : AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily
      (Over.mk (Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))) :=
    ⟨F.val, F.property.1, F.property.2.2⟩
  exact G.pullbackAlong (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom (𝟙 (Spec (CommRingCat.of R)))
    (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_isPullback n a)

theorem affineNativeToPolynomial_ideal
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :
    (affineNativeToPolynomial n a F).ideal = F.val.comap (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom := rfl

def affinePolynomialToNative
    (F : AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)))) :
    Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) := by
  let k := F.ideal.subschemeι ≫ (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom
  have hk : k ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) =
      F.ideal.subschemeι ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) := by
    rw [Category.assoc, ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projection]
  have : IsProper (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)) := polynomialProjectiveStructureMap_proper n
  have : IsClosedImmersion k := inferInstanceAs
    (IsClosedImmersion (F.ideal.subschemeι ≫ (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom))
  have : Flat (k ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) := hk.symm ▸ F.flat
  have : LocallyOfFinitePresentation (k ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :=
    hk.symm ▸ F.locallyFinitePresentation
  have : IsProper (k ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) :=
    hk.symm ▸ (inferInstanceAs (IsProper (F.ideal.subschemeι ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))))
  exact Closed.ImmersionFamily.Hilbert.closedImmersionFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) k

theorem affinePolynomialToNative_ideal
    (F : AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)))) :
    (affinePolynomialToNative n a F).val = F.ideal.comap (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).inv := by
  change (F.ideal.subschemeι ≫ (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom).ker = _
  rw [Global.PolynomialInclusion.closedImmersion_comp_iso_ker, Scheme.IdealSheafData.ker_subschemeι]

def affineNativePolynomialFamilyEquiv : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) ≃
    AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))) where
  toFun := affineNativeToPolynomial n a
  invFun := affinePolynomialToNative n a
  left_inv F := by
    apply Subtype.ext
    rw [affinePolynomialToNative_ideal, affineNativeToPolynomial_ideal,
      ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  right_inv F := by
    apply AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily.ext
    rw [affineNativeToPolynomial_ideal, affinePolynomialToNative_ideal,
      ← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicPolynomialFamily.GradedHilbert
