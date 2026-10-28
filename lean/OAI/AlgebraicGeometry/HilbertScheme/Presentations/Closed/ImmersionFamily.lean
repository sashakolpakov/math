import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Immersion Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionFamily.Hilbert

noncomputable section

/-! A flat proper finitely presented closed immersion defines the actual
ideal-sheaf family used by the native Hilbert functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) {T : Over S} {Z : Scheme.{u}}
variable (f : Z ⟶ Hilbert.Functor.ambient X T) [IsClosedImmersion f]

omit [IsClosedImmersion f] in
theorem closedImmersion_image_projection :
    f.toImage ≫ Hilbert.Functor.familyProjection X f.ker = f ≫ Hilbert.Functor.ambientProjection X T := by
  change f.toImage ≫ (f.imageι ≫ Hilbert.Functor.ambientProjection X T) = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι]

theorem closedImmersion_isFamily [Flat (f ≫ Hilbert.Functor.ambientProjection X T)]
    [IsProper (f ≫ Hilbert.Functor.ambientProjection X T)] [LocallyOfFinitePresentation (f ≫ Hilbert.Functor.ambientProjection X T)] :
    Hilbert.Functor.IsFamily X f.ker := by
  have : IsIso f.toImage := inferInstance
  have he : Hilbert.Functor.familyProjection X f.ker = inv f.toImage ≫ (f ≫ Hilbert.Functor.ambientProjection X T) :=
    (Iso.eq_inv_comp (asIso f.toImage)).mpr (closedImmersion_image_projection X f)
  change Flat (Hilbert.Functor.familyProjection X f.ker) ∧ IsProper (Hilbert.Functor.familyProjection X f.ker) ∧
    LocallyOfFinitePresentation (Hilbert.Functor.familyProjection X f.ker)
  rw [he]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def closedImmersionFamily [Flat (f ≫ Hilbert.Functor.ambientProjection X T)]
    [IsProper (f ≫ Hilbert.Functor.ambientProjection X T)] [LocallyOfFinitePresentation (f ≫ Hilbert.Functor.ambientProjection X T)] :
    Hilbert.Functor.Family X T := ⟨f.ker, closedImmersion_isFamily X f⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionFamily.Hilbert
