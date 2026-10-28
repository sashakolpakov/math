import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective
import Mathlib.AlgebraicGeometry.Birational.Birational

/-! # Resolution Geometry -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ResolutionGeometry.Construction

/-!
Supporting geometry for Blowups. This file does not import the statement stub.
The existence of a smooth projective resolution is not yet proved here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The smooth locus of an integral projective complex scheme is dense. -/
theorem smoothLocus_dense
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) :
    letI : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
    Dense (f.smoothLocus : Set X) := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  exact f.dense_smoothLocus_of_perfectField

/-- Restricting the structure map to its smooth locus gives a smooth morphism. -/
theorem smooth_on_smoothLocus
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) :
    letI : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
    Smooth (f.smoothLocus.ι ≫ f) := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  ext x
  simp

/-- A map over the complex base from a projective variety to a projective
scheme is proper. This does not require the map to resolve singularities. -/
theorem proper_of_projective_over
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f)
    (R : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : R.carrier ⟶ X)
    (hπ : π ≫ f = R.structureMap) : IsProper π := by
  let : IsProper f := P.isProper
  let : IsProper (π ≫ f) := hπ.symm ▸ R.presentation.projective.isProper
  exact IsProper.of_comp π f

/-- An isomorphism over a dense open of the target gives a partial isomorphism
compatible with the original map when the source is irreducible. -/
theorem partialIso_of_isIso_restriction
    {R X : Scheme} [IrreducibleSpace R] [Nonempty X]
    (π : R ⟶ X) (U : X.Opens) (hU : Dense (U : Set X))
    [IsIso (π ∣_ U)] :
    ∃ e : R.PartialIso X,
      e.source.ι ≫ π = e.iso.hom ≫ e.target.ι := by
  obtain ⟨x, hx⟩ := hU.nonempty
  let r : (π ⁻¹ᵁ U).toScheme := (inv (π ∣_ U)) ⟨x, hx⟩
  have hpre : ((π ⁻¹ᵁ U) : Set R).Nonempty := ⟨r.1, r.2⟩
  refine ⟨{
    source := π ⁻¹ᵁ U
    dense_source := (π ⁻¹ᵁ U).isOpen.dense hpre
    target := U
    dense_target := hU
    iso := asIso (π ∣_ U)
  }, ?_⟩
  exact (morphismRestrict_ι π U).symm

end OAI.AlgebraicGeometry.Resolution.Blowups.ResolutionGeometry.Construction
