import OAI.AlgebraicGeometry.Comparison.Betti.SchemeProductTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeClosed
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.Metrizable.Urysohn

/-! # Separated Point Topology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SeparatedPointTopology

noncomputable section

/-!
# Separated schemes have Hausdorff complex points

The genuine scheme diagonal is a closed immersion. The proved product
homeomorphism identifies its analytic image with the ordinary diagonal.
Finite type then gives local compactness and second countability, hence
metrizability without a separately supplied analytic hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def schemeDiagonal : X ⟶ SchemeProductTopology.productScheme X X := SchemeProductTopology.productLift X X (𝟙 X) (𝟙 X)

theorem schemeDiagonal_point (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    SchemeProductTopology.productPointsHomeomorph X X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (schemeDiagonal X) p) = (p, p) := by
  apply Prod.ext
  · change (p ≫ SchemeProductTopology.productLift X X (𝟙 X) (𝟙 X)) ≫ SchemeProductTopology.productLeft X X = p
    rw [Category.assoc, SchemeProductTopology.productLift_left, Category.comp_id]
  · change (p ≫ SchemeProductTopology.productLift X X (𝟙 X) (𝟙 X)) ≫ SchemeProductTopology.productRight X X = p
    rw [Category.assoc, SchemeProductTopology.productLift_right, Category.comp_id]

theorem separated_complexPoints_t2Space [IsSeparated X.hom] :
    T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  have : IsClosedImmersion (schemeDiagonal X).left :=
    inferInstanceAs (IsClosedImmersion (pullback.diagonal X.hom))
  have hd := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (schemeDiagonal X)).isClosed_range
  have h := (SchemeProductTopology.productPointsHomeomorph X X).isClosedMap _ hd
  rw [← Set.range_comp] at h
  have heq : (SchemeProductTopology.productPointsHomeomorph X X) ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (schemeDiagonal X) = Function.diag := by
    funext p
    exact schemeDiagonal_point X p
  rw [heq, Set.range_diag] at h
  exact t2_iff_isClosed_diagonal.mpr h

theorem finiteType_separated_complexPoints_metrizable
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  have := separated_complexPoints_t2Space X
  have := ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_locallyCompact X
  have := ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable X
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.SeparatedPointTopology
