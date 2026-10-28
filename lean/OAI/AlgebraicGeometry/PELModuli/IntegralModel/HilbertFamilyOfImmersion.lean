import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Hilbert Family Of Immersion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertFamilyOfImmersion

noncomputable section

/-! An actual flat proper finitely presented closed immersion in a
relative product gives a Hilbert family, with its source recovered. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme.{0}} (X T : Over S) {Z : Scheme.{0}}
    (j : Z ⟶ HilbertScheme.Presentations.Hilbert.Functor.ambient X T) [IsClosedImmersion j]

omit [IsClosedImmersion j] in
theorem hilbertFamily_image_projection :
    j.toImage ≫ HilbertScheme.Presentations.Hilbert.Functor.familyProjection X j.ker = j ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T := by
  change j.toImage ≫ (j.imageι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T) = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]

theorem hilbertFamily_of_closed_immersion
    [Flat (j ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T)]
    [IsProper (j ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T)]
    [LocallyOfFinitePresentation (j ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T)] :
    HilbertScheme.Presentations.Hilbert.Functor.IsFamily X j.ker := by
  have h : HilbertScheme.Presentations.Hilbert.Functor.familyProjection X j.ker =
      inv j.toImage ≫ (j ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T) :=
    (Iso.eq_inv_comp (asIso j.toImage)).mpr (hilbertFamily_image_projection X T j)
  rw [HilbertScheme.Presentations.Hilbert.Functor.IsFamily, h]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def hilbertFamilyOfClosedImmersion
    [Flat (j ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T)]
    [IsProper (j ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T)]
    [LocallyOfFinitePresentation (j ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection X T)] : HilbertScheme.Presentations.Hilbert.Functor.Family X T :=
  ⟨j.ker, hilbertFamily_of_closed_immersion X T j⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertFamilyOfImmersion
