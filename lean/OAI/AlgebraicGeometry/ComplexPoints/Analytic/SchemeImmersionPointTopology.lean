import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed
import OAI.AlgebraicGeometry.Foundations.Scheme.ImmersionComplexPoints
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Topology.LocallyClosed

/-! # Scheme Immersion Point Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Immersions on ordinary complex-valued scheme points

The factorization used here is mathlib's actual coborder factorization of a
scheme immersion into a closed immersion followed by an open immersion.
The ordinary point topology is the established affine-test topology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The genuine open intermediate scheme in the coborder factorization,
with its inherited complex structure morphism. -/
def SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget (φ : X ⟶ Y) [IsImmersion φ.left] : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (φ.left.coborderRange.ι ≫ Y.hom)

/-- The closed part of the actual immersion factorization, over `Spec ℂ`. -/
def SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    X ⟶ SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget φ :=
  Over.homMk φ.left.liftCoborder (by
    change φ.left.liftCoborder ≫ (φ.left.coborderRange.ι ≫ Y.hom) = X.hom
    rw [← Category.assoc, Scheme.Hom.liftCoborder_ι]
    exact φ.w)

/-- The open part of the actual immersion factorization, over `Spec ℂ`. -/
def SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget φ ⟶ Y :=
  Over.homMk φ.left.coborderRange.ι rfl

instance SchemePointHomeomorphs.schemeComplexPoints.isClosedImmersion_immersionClosedFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    IsClosedImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ).left :=
  inferInstanceAs (IsClosedImmersion φ.left.liftCoborder)

instance SchemePointHomeomorphs.schemeComplexPoints.isOpenImmersion_immersionOpenFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    IsOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ).left :=
  inferInstanceAs (IsOpenImmersion φ.left.coborderRange.ι)

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor_comp_openFactor (φ : X ⟶ Y) [IsImmersion φ.left] :
    SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ ≫ SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ = φ := by
  apply Over.OverMorphism.ext
  exact φ.left.liftCoborder_ι

/-- On native complex points, the actual immersion is the composition of
the induced closed and open point maps. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.map_immersion_factorization (φ : X ⟶ Y) [IsImmersion φ.left] :
    SchemePointHomeomorphs.schemeComplexPoints.map φ = SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ) ∘ SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) := by
  funext p
  change p ≫ φ = (p ≫ SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) ≫ SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ
  rw [Category.assoc, SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor_comp_openFactor]

/-- An actual scheme immersion induces an embedding of ordinary complex
point spaces. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left] :
    Topology.IsEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map φ) := by
  rw [SchemePointHomeomorphs.schemeComplexPoints.map_immersion_factorization]
  exact (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ)).isEmbedding.comp
    (SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ)).isEmbedding

/-- The ordinary complex-point image of an actual immersion is locally
closed, by its genuine closed-then-open factorization. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosed_range_map_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left] :
    IsLocallyClosed (Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ)) := by
  rw [SchemePointHomeomorphs.schemeComplexPoints.map_immersion_factorization, Set.range_comp]
  have hc := SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ)
  have ho := SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ)
  exact hc.isClosed_range.isLocallyClosed.image ho.isEmbedding.isInducing
    ho.isOpen_range.isLocallyClosed

/-- The two standard requirements for a locally closed embedding hold for
the induced ordinary complex-point map. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosedEmbedding_map_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left] :
    Topology.IsEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map φ) ∧ IsLocallyClosed (Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ)) :=
  ⟨SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ, SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosed_range_map_of_isImmersion φ⟩

/-- Surjectivity on the actual scheme stalks gives exactly the complex
points lying over the underlying image, by the proved residue-field lift. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.range_map_of_surjectiveOnStalks (φ : X ⟶ Y) [SurjectiveOnStalks φ.left] :
    Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ) = SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range φ.left :=
  Foundations.Scheme.ImmersionComplexPoints.range_surjectiveOnStalks_complexPointMap φ

/-- The native point image of an actual immersion is precisely the inverse
image of its underlying scheme image. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion (φ : X ⟶ Y) [IsImmersion φ.left] :
    Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ) = SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range φ.left :=
  SchemePointHomeomorphs.schemeComplexPoints.range_map_of_surjectiveOnStalks φ

/-- Native points of the immersed scheme are homeomorphic to the genuine
locally closed subset specified by its underlying image. -/
def SchemePointHomeomorphs.schemeComplexPoints.immersionPointHomeomorph (φ : X ⟶ Y) [IsImmersion φ.left] :
    SchemePointHomeomorphs.schemeComplexPoints X ≃ₜ (SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range φ.left) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ).toHomeomorph.trans
    (Homeomorph.setCongr (SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion φ))

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.immersionPointHomeomorph_val (φ : X ⟶ Y) [IsImmersion φ.left]
    (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    (SchemePointHomeomorphs.schemeComplexPoints.immersionPointHomeomorph φ p).val = SchemePointHomeomorphs.schemeComplexPoints.map φ p := rfl

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
