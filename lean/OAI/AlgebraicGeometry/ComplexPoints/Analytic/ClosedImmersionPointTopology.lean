import OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.QuotientPointTopology

/-! # Closed Immersion Point Topology -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Ordinary topology of affine closed immersions

A surjective complex algebra map induces a closed embedding of its actual
complex-point spaces. The image is exactly the common zero locus of its kernel.
Mathlib's characterization of affine scheme closed immersions then applies
this result to the actual spectrum map, rather than an assumed presentation.
-/

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- A surjective algebra map identifies target points with the zero locus of its kernel. -/
def Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph (f : A →ₐ[ℂ] B) (hf : Function.Surjective f) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints B ≃ₜ Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus (RingHom.ker f) :=
  (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comapHomeomorph (Ideal.quotientKerAlgEquivOfSurjective hf)).trans
    (ComplexPoints.Analytic.QuotientPointTopology.quotientComplexPointsHomeomorph (RingHom.ker f))

/-- The homeomorphism is the actual precomposition map on algebra characters. -/
@[simp]
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph_val (f : A →ₐ[ℂ] B) (hf : Function.Surjective f)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf x).val = x.comp f := by
  ext a
  rfl

/-- The image of a surjective algebra map on complex points is its kernel zero locus. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.range_comap_of_surjective (f : A →ₐ[ℂ] B) (hf : Function.Surjective f) :
    Set.range (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) = Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus (RingHom.ker f) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change y.comp f ∈ Foundations.Scheme.QuotientComplexPoints.affineIdealZeroLocus (RingHom.ker f)
    rw [← Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph_val f hf y]
    exact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf y).property
  · intro hx
    refine ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf).symm ⟨x, hx⟩, ?_⟩
    change ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf).symm ⟨x, hx⟩).comp f = x
    rw [← Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph_val f hf]
    exact congrArg Subtype.val ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf).apply_symm_apply ⟨x, hx⟩)

/-- A surjective algebra map induces a closed embedding for ordinary complex-point topologies. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective (f : A →ₐ[ℂ] B)
    (hf : Function.Surjective f) : Topology.IsClosedEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) := by
  have heq : (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B => (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf x).val) =
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f := by
    funext x
    exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph_val f hf x
  rw [← heq]
  exact (ComplexPoints.Analytic.QuotientPointTopology.isClosed_affineIdealZeroLocus (RingHom.ker f)).isClosedEmbedding_subtypeVal.comp
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.surjectiveComapHomeomorph f hf).isClosedEmbedding

/-- A genuine affine spectrum closed immersion induces an ordinary closed point embedding. -/
theorem Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_spec_closedImmersion
    {A B : Type u} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B)
    [AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom))] :
    Topology.IsClosedEmbedding (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) :=
  Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective f
    (Foundations.Scheme.AffineClosedImmersion.ringMap_surjective_of_spec_closedImmersion (CommRingCat.ofHom f.toRingHom))

end

end OAI.AlgebraicGeometry
