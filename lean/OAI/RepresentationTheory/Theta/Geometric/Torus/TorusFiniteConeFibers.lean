import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusImageCharts
import OAI.Geometry.ComplexTorus.RiemannProjectivity.CompactAnalyticAt
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConeProjection

/-! # Torus Finite Cone Fibers -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers

noncomputable section

open Set
open scoped _root_.Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem holomorphic_inter {S T : Set V} {x : V}
    (hS : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x) (hT : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T x) :
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (S ∩ T) x := by
  obtain ⟨U, hU, hxU, m, f, hf, heqf⟩ := hS
  obtain ⟨D, hD, hxD, n, g, hg, heqg⟩ := hT
  refine ⟨U ∩ D, hU.inter hD, ⟨hxU, hxD⟩, m + n, Fin.addCases f g, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left j => simpa only [Fin.addCases_left] using (hf j).mono (inter_subset_left (t := D))
    | right j => simpa only [Fin.addCases_right] using (hg j).mono (inter_subset_right (s := U))
  · intro y hy
    change (y ∈ S ∧ y ∈ T) ↔ _
    rw [heqf y hy.1, heqg y hy.2]
    simp only [Fin.forall_fin_add, Fin.addCases_left, Fin.addCases_right]

theorem holomorphic_linear_fiber [FiniteDimensional ℂ W]
    (L : V →L[ℂ] W) (y : W) (x : V) : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt {v | L v = y} x := by
  let e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨univ, isOpen_univ, mem_univ x, Module.finrank ℂ W,
    (fun i v => e (L v - y) i), ?_, ?_⟩
  · intro i
    exact differentiableOn_pi.mp
      (e.differentiable.comp (L.differentiable.sub_const y)).differentiableOn i
  · intro v _
    constructor
    · intro hv i
      change L v = y at hv
      simp only [hv, sub_self, map_zero, Pi.zero_apply]
    · intro hv
      apply sub_eq_zero.mp
      apply e.injective
      rw [map_zero]
      exact funext hv

theorem finite_proper_cone_fiber [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    {S : Set V} (L : V →L[ℂ] W)
    (hproper : IsProperMap (fun v : S => L v))
    (hkernel : ∀ v ∈ S, L v = 0 → v = 0)
    (hlocal : ∀ v ∈ S, v ≠ 0 → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) (y : W) :
    {v : V | v ∈ S ∧ L v = y}.Finite := by
  by_cases hy : y = 0
  · subst y
    exact (finite_singleton (0 : V)).subset
      (fun v hv => hkernel v hv.1 hv.2)
  · have hcompact : IsCompact {v : V | v ∈ S ∧ L v = y} := by
      have h := (hproper.isCompact_preimage (isCompact_singleton (x := y))).image
        continuous_subtype_val
      convert! h using 1
      ext v
      simp only [mem_ofPred_eq, mem_image, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨hv, hL⟩ => ⟨⟨v, hv⟩, hL, rfl⟩,
        fun ⟨w, hw, he⟩ => he ▸ ⟨w.property, hw⟩⟩
    apply Geometry.ComplexTorus.RiemannProjectivity.CompactAnalyticAt.Constructions.CompactAnalytic.finite_of_isCompact_holomorphic hcompact
    intro v hv
    have hv0 : v ≠ 0 := by
      intro hz
      exact hy (by simpa only [hz, map_zero] using hv.2.symm)
    exact holomorphic_inter (hlocal v hv.1 hv0) (holomorphic_linear_fiber L y v)

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

theorem cone_holomorphic_of_period_embedding {n : ℕ} (Φ : Data.CM.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Topology.IsClosedEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) →
        DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
        Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) :
    ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), v ≠ 0 → AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v := by
  apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.holomorphicZeroSetAt_projectiveCone
  rintro i p ⟨t, rfl⟩ hi
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  let U : Set (Φ.space) := {w | AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk w))}
  have hU : IsOpen U := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage
    (hf.continuous.comp QuotientAddGroup.continuous_mk)
  have hn := TorusImageCharts.CM.Algebraization.ImageCharts.hasHolomorphicNormalChart_of_injective_fderiv
    (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z hU hi
    (fun w hw => (hd w i hw).1.differentiableWithinAt) (hd z i hi).2
  obtain ⟨m, O, g, hO, hx, hg, heq⟩ := TorusImageCharts.CM.Algebraization.ImageCharts.local_equations_for_embedded_image
    (QuotientAddGroup.mk : Φ.space → Φ.periodTorus)
    QuotientAddGroup.continuous_mk QuotientAddGroup.isOpenMap_coe f hf.isEmbedding
    (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i) (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_target i) z hi hn
  refine ⟨O, hO, hx, m, fun j y => g y j,
    fun j => differentiableOn_pi.mp hg j, ?_⟩
  intro y hy
  change (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm y ∈ range f ↔ ∀ j, g y j = 0
  rw [← heq y hy]
  exact funext_iff

/-- The actual projective CM cone has a proper linear projection of the
expected target dimension, and every fiber is finite. -/
theorem proper_finite_period_cone_projection
    (Φ : Data.CM.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      IsProperMap (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      (∀ y, {v : Fin (n + 1) → ℂ | v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L v = y}.Finite) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), ‖v‖ ≤ C * ‖L v‖ := by
  obtain ⟨n, f, hf, hd⟩ := Root.CM.Algebraization.projective_period_torus_all_charts Φ
  obtain ⟨L, hL⟩ := TorusConeProjection.CM.Algebraization.ConeProjection.projection_of_period_embedding Φ f hf.continuous
    (fun z i hi => (hd z i hi).1)
  have hclosed := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hproper := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hclosed (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) L hL
  exact ⟨n, f, L, hf, hproper,
    finite_proper_cone_fiber L hproper hL (cone_holomorphic_of_period_embedding Φ f hf hd),
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.norm_le_projection hclosed (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) L hL⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers
