import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ClosedImmersionPointTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointClosedMap

/-! # Scheme Closed -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Closed immersions on genuine complex scheme points

Every closed immersion of schemes over the complex base induces a closed
topological embedding for the affine-test topology. The proof first treats
affine schemes using their actual global-section algebras, then tests an
arbitrary closed image on affine spaces. Actual scheme pullbacks identify each
test preimage with the image under an affine closed immersion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- An affine closed immersion is a closed embedding on its genuine complex-valued points. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isAffine
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) [IsClosedImmersion f.left] :
    Topology.IsClosedEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  have hsurj : Function.Surjective (AffineSchemePointTopology.affineCoordinateHom f) := by
    change Function.Surjective (AffineSchemePointTopology.affineCoordinateHom f).toRingHom
    rw [AffineSchemePointTopology.affineCoordinateHom_toRingHom]
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2
  rw [AffineSchemePointTopology.schemePointMap_eq_affineCoordinates f]
  exact (AffineSchemePointTopology.affineNativePointHomeomorph Y).symm.isClosedEmbedding.comp
    ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isClosedEmbedding_comap_of_surjective
      (AffineSchemePointTopology.affineCoordinateHom f) hsurj).comp (AffineSchemePointTopology.affineNativePointHomeomorph X).isClosedEmbedding)

/-- A closed immersion gives an injective map on genuine complex-valued points. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.map_injective_of_isClosedImmersion (f : X ⟶ Y) [IsClosedImmersion f.left] :
    Function.Injective (SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply (cancel_mono f.left).mp
  exact congrArg Over.Hom.left h

/-- Closed immersions send all closed sets of complex-valued points to closed sets. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosedMap_map_of_isClosedImmersion (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedMap (SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  apply SchemePointHomeomorphs.schemeComplexPoints.isClosedMap_map_of_affine_pullbacks f
  intro A g
  have : IsClosedImmersion (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g).left := by
    change IsClosedImmersion (pullback.snd f.left g.left)
    infer_instance
  have : IsAffine (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left := by
    change IsAffine (Spec (CommRingCat.of A))
    infer_instance
  have : IsAffine (SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f g).left :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g).left).1
  exact (SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isAffine (SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f g)).isClosedMap

/-- A closed immersion is a closed point embedding for the affine-test topology. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    Topology.IsClosedEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map f) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (SchemePointHomeomorphs.schemeComplexPoints.continuous_map f) (SchemePointHomeomorphs.schemeComplexPoints.map_injective_of_isClosedImmersion f)
    (SchemePointHomeomorphs.schemeComplexPoints.isClosedMap_map_of_isClosedImmersion f)

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
