import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeIntegralProper
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Affine Scheme Graph -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.AffineSchemeGraph.Constructions

noncomputable section

/-! Every finite map to an affine complex scheme has an actual closed polynomial graph with a compact coordinate bound over a base neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_bounded_finite_graph {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine Y.left]
    [LocallyOfFiniteType Y.hom] (g : X ⟶ Y) [IsFinite g.left] (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    letI : IsAffine X.left := isAffine_of_isAffineHom g.left
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
      (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (K : Set (Fin n → ℂ)),
      Function.Surjective f ∧ IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left ∧
      x ∈ U ∧ IsCompact K ∧
      Topology.IsClosedEmbedding (GraphBaseRestriction.Constructions.restrictedGraph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g)
        (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) ∧
      Set.range (GraphBaseRestriction.Constructions.restrictedGraph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g)
        (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) ⊆ Set.univ ×ˢ K := by
  let : IsAffine X.left := isAffine_of_isAffineHom g.left
  let : LocallyOfFiniteType X.hom := by
    rw [← g.w]
    infer_instance
  let : LocallyCompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineSchemePoints_locallyCompact Y
  let : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph Y).isEmbedding.t2Space
  obtain ⟨n, f, hf, hscheme⟩ := Affine.SchemeGraph.Constructions.exists_globalGraphSchemeMap g
  have hp := Affine.SchemeIntegralProper.Constructions.isProperMap_affine_integral g
  obtain ⟨U, K, hx, hK, hbound⟩ := Affine.SchemeGraphAnalytic.Constructions.globalGraph_localBound g f hp x
  exact ⟨n, f, U, K, hf, hscheme, hx, hK,
    GraphBaseRestriction.Constructions.restrictedGraph_closedEmbedding (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f)
      U (Affine.SchemeGraphAnalytic.Constructions.globalGraph_closedEmbedding g f hf),
    GraphBaseRestriction.Constructions.restrictedGraph_bound (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) U K hbound⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.AffineSchemeGraph.Constructions
