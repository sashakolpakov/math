import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDetection
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical

/-! # Slice -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Slice.Constructions.Class

noncomputable section

/-! The actual normal slice sends the immersion-chart Thom class to the original open normal generator. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.SliceDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {c : ℕ} {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin c → ℂ) f x)

omit [NormedSpace ℝ E] in
theorem normalSlice_first (u : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) :
    HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P (SliceDetection.Constructions.normalSliceMap P u) = (u, SliceDetection.Constructions.tangentOrigin P) :=
  (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P).apply_symm_apply (u, SliceDetection.Constructions.tangentOrigin P)

omit [NormedSpace ℝ E] in
theorem normalSlice_normal : SliceDetection.Constructions.normalSliceMap P ≫ P.normalCoordinate =
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Fin c → ℂ)) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P : Set (Fin c → ℂ)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  exact congrArg (fun z : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P × HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P => z.1.val)
    (normalSlice_first P u)

omit [NormedSpace ℝ E] in
theorem normalSlice_origin : SliceDetection.Constructions.normalSliceMap P (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P) =
    ⟨f x, P.point_mem_neighborhood⟩ := by
  apply (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P).injective
  rw [normalSlice_first]
  change (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOrigin P, SliceDetection.Constructions.tangentOrigin P) =
    ((P.homeomorph ⟨f x, P.point_mem_neighborhood⟩).2,
      (P.homeomorph ⟨f x, P.point_mem_neighborhood⟩).1)
  rw [P.homeomorph_point]
  rfl

theorem normalSlice_class :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SliceDetection.Constructions.normalSliceMap P) (SliceDetection.Constructions.normalSliceMapsTo P)
      (2 * c) P.rationalClassFin =
    HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOriginRelativeDualClass (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos) := by
  rw [P.rationalClassFin_eq_normalPullback]
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (SliceDetection.Constructions.normalSliceMap P) P.normalCoordinate
      (SliceDetection.Constructions.normalSliceMapsTo P) P.normalCoordinate_mapsTo (2 * c)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c)
  refine hc.trans ?_
  exact ConcreteCategory.congr_hom (Product.PointCanonical.Constructions.Class.relativeMap_congr (normalSlice_normal P)
    (P.normalCoordinate_mapsTo.comp (SliceDetection.Constructions.normalSliceMapsTo P))
    (HodgeConjecture.DegreeTwo.NestedOpenPointClass.Constructions.openOrigin_mapsTo_complement (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairNormalOpen P) (Metric.mem_ball_self P.radius_pos))
    (2 * c)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Slice.Constructions.Class
