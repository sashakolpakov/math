import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeProjection
import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt

/-! # Algebraic Regular Cone -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicRegularCone.CM.Abelian.Algebraization.RegularCone

noncomputable section

open Set

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

theorem regular_projection_of_period_embedding {n : ℕ} (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Continuous f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) → DifferentiableAt ℂ
        (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)
    (A : (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ))
    (hA : Function.Injective A) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ),
      (∀ v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0) ∧ Function.Bijective (L.comp A) := by
  let g : Φ.space → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun z => f (QuotientAddGroup.mk z)
  let U : Fin (n + 1) → Set (Φ.space) :=
    fun i => g ⁻¹' (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
  let r : Fin (n + 1) → Φ.space → Fin n → ℂ :=
    fun i z => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z)
  have hg : Continuous g := hf.comp QuotientAddGroup.continuous_mk
  have hU : ∀ i, IsOpen (U i) := fun i => (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage hg
  have hr : ∀ i, DifferentiableOn ℂ (r i) (U i) :=
    fun i z hz => (hd z i hz).differentiableWithinAt
  apply Geometry.ComplexTorus.RiemannProjectivity.RegularProjectionIs.Constructions.RegularProjection.exists_regular_projection_avoiding (Nat.lt_succ_self _) U r hU hr
    (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) ?_ A hA
  intro v hv hv0
  obtain ⟨t, ht⟩ := hv hv0
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨i, hi⟩ := ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (Projectivization.mk ℂ v hv0)
  have hgz : g z = Projectivization.mk ℂ v hv0 := by simp only [g, hz, ht]
  refine ⟨i, z, ?_, (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv0).mp hi, ?_⟩
  · change g z ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
    rwa [hgz]
  · intro j
    change v (i.succAbove j) / v i = ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z) j
    rw [hgz, ← ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize_eq_projectiveChart i v hv0]
    rfl

/-- The actual cone admits a proper linear projection whose image contains
a nonempty open set of the base. -/
theorem proper_period_cone_projection_with_interior_and_immersions
    (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ (z : Φ.space) (i : Fin (n + 1)),
        f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
        Function.Injective (fderiv ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)) ∧
      (∀ v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0) ∧
      IsProperMap (fun v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      (interior (L '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))).Nonempty := by
  obtain ⟨n, f, hf, hd⟩ := AlgebraizationRoot.CM.Abelian.Algebraization.projective_period_torus_all_charts Φ
  let g : Φ.space → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun z => f (QuotientAddGroup.mk z)
  obtain ⟨i, hi⟩ := ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (g 0)
  let r : Φ.space → Fin n → ℂ := fun z => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z)
  let U : Set (Φ.space) := g ⁻¹' (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
  have hU : IsOpen U := (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage
    (hf.continuous.comp QuotientAddGroup.continuous_mk)
  have hr : DifferentiableOn ℂ r U := fun z hz => (hd z i hz).1.differentiableWithinAt
  let T := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.tangentMap i r 0
  have hT : Function.Injective T := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.tangentMap_injective i (hd 0 i hi).2
  let e : (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) ≃L[ℂ]
      (Φ.space × ℂ) := ContinuousLinearEquiv.ofFinrankEq (by
    simp [Module.finrank_prod])
  let A := T.comp e.toContinuousLinearMap
  have hA : Function.Injective A := hT.comp e.injective
  obtain ⟨L, hL, hreg⟩ := regular_projection_of_period_embedding Φ f hf.continuous
    (fun z j hz => (hd z j hz).1) A hA
  have hLT : Function.Bijective (L.comp T) :=
    (Function.Bijective.of_comp_iff (L.comp T) e.bijective).mp hreg
  let F : (Φ.space × ℂ) → (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) :=
    fun p => L (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i r p)
  have hFd : HasFDerivAt F (L.comp T) (0, 1) :=
    L.hasFDerivAt.comp (0, 1) (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.hasFDerivAt_parameterization i (hd 0 i hi).1)
  have hFdiff : DifferentiableOn ℂ F (U ×ˢ univ) :=
    L.differentiable.comp_differentiableOn (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.differentiableOn_parameterization i hr)
  have hFreg : Function.Bijective (fderiv ℂ F (0, 1)) := by rwa [hFd.fderiv]
  have hxU : (0, (1 : ℂ)) ∈ U ×ˢ univ := ⟨hi, mem_univ _⟩
  obtain ⟨q, hq, hqF, _⟩ := Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt.Constructions.FiniteBranches.holomorphic_local_inverse
    (hU.prod isOpen_univ) hFdiff hxU hFreg
  let q' := q.restrOpen (U ×ˢ univ) (hU.prod isOpen_univ)
  have hq' : (0, (1 : ℂ)) ∈ q'.source := ⟨hq, hi, mem_univ _⟩
  have hsubset : q'.target ⊆ L '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    intro y hy
    let p := q'.symm y
    have hp : p ∈ q'.source := q'.map_target hy
    have hmem : Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i r p ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
      have h := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization_mem_cone i g p.1 hp.2.1 p.2
      intro hv0
      obtain ⟨z, hz⟩ := h hv0
      exact ⟨QuotientAddGroup.mk z, hz⟩
    refine ⟨Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i r p, hmem, ?_⟩
    have hqp : q' p = F p := congrFun hqF p
    exact hqp.symm.trans (q'.right_inv hy)
  refine ⟨n, f, L, hf, hd, hL, ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection
    (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone _ hf.isClosed_range) (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _) L hL, ?_⟩
  exact ⟨q' (0, 1), interior_mono hsubset
    ((q'.open_target.interior_eq).symm ▸ q'.map_source hq')⟩

theorem proper_period_cone_projection_with_interior_and_charts
    (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ (z : Φ.space) (i : Fin (n + 1)),
        f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z) ∧
      (∀ v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0) ∧
      IsProperMap (fun v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      (interior (L '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))).Nonempty := by
  obtain ⟨n, f, L, hf, hd, hL, hp, hi⟩ :=
    proper_period_cone_projection_with_interior_and_immersions Φ
  exact ⟨n, f, L, hf, (fun z i hi => (hd z i hi).1), hL, hp, hi⟩

theorem proper_period_cone_projection_with_interior
    (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0) ∧
      IsProperMap (fun v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      (interior (L '' ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))).Nonempty := by
  obtain ⟨n, f, L, hf, _, hL, hp, hi⟩ :=
    proper_period_cone_projection_with_interior_and_charts Φ
  exact ⟨n, f, L, hf, hL, hp, hi⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicRegularCone.CM.Abelian.Algebraization.RegularCone
