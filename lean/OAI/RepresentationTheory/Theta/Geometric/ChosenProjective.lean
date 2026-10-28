import OAI.RepresentationTheory.Theta.Geometric.Torus.SmoothProjectiveModel

/-! # Chosen Projective -/

namespace OAI.RepresentationTheory.Theta.Geometric.ChosenProjective.CM.Torus.Algebraization.ChosenProjectiveModel

noncomputable section

/-! Algebraize a supplied projective embedding, retaining its exact map. -/

open Set _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure

variable {n : ℕ} (Φ : Torus.Data.CM.ProjectivePeriodData)
  (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
  (hf : Topology.IsClosedEmbedding f)
  (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
    f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
    DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
    Function.Injective (fderiv ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z))

include hf hd

theorem regular_projection :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ Φ.space + 1) → ℂ),
      (∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0) ∧
      IsProperMap (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      (interior (L '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))).Nonempty := by
  let g : Φ.space → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun z => f (QuotientAddGroup.mk z)
  obtain ⟨i, hi⟩ := AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (g 0)
  let r : Φ.space → Fin n → ℂ := fun z => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z)
  let U : Set (Φ.space) := g ⁻¹' (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
  have hU : IsOpen U := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage
    (hf.continuous.comp QuotientAddGroup.continuous_mk)
  have hr : DifferentiableOn ℂ r U := fun z hz => (hd z i hz).1.differentiableWithinAt
  let T := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.tangentMap i r 0
  have hT : Function.Injective T := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.tangentMap_injective i (hd 0 i hi).2
  let e : (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) ≃L[ℂ]
      (Φ.space × ℂ) := ContinuousLinearEquiv.ofFinrankEq (by
    simp [Module.finrank_prod])
  let A := T.comp e.toContinuousLinearMap
  have hA : Function.Injective A := hT.comp e.injective
  obtain ⟨L, hL, hreg⟩ := Torus.TorusRegularCone.CM.Algebraization.RegularCone.regular_projection_of_period_embedding Φ f hf.continuous
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
  have hsubset : q'.target ⊆ L '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    intro y hy
    let p := q'.symm y
    have hp : p ∈ q'.source := q'.map_target hy
    have hmem : Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i r p ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
      have h := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization_mem_cone i g p.1 hp.2.1 p.2
      intro hv0
      obtain ⟨z, hz⟩ := h hv0
      exact ⟨QuotientAddGroup.mk z, hz⟩
    refine ⟨Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i r p, hmem, ?_⟩
    have hqp : q' p = F p := congrFun hqF p
    exact hqp.symm.trans (q'.right_inv hy)
  refine ⟨L, hL, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone _ hf.isClosed_range) (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _) L hL, ?_⟩
  exact ⟨q' (0, 1), interior_mono hsubset
    ((q'.open_target.interior_eq).symm ▸ q'.map_source hq')⟩

theorem homogeneous_equations :
    ∃ Q : Finset (MvPolynomial (Fin (n + 1)) ℂ),
      (∀ q ∈ Q, ∃ k, q.IsHomogeneous k) ∧
      AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) = {v | ∀ q ∈ Q, MvPolynomial.eval v q = 0} := by
  obtain ⟨L, hker, _, hi⟩ := regular_projection Φ f hf hd
  have hclosed := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hsurj := Torus.TorusConeSurjectivity.CM.Algebraization.ConeSurjectivity.surjective_cone_projection L hclosed (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _)
    hker (Torus.TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd) hi
  exact Geometry.ComplexTorus.RiemannProjectivity.PolynomialSeparationFinite.Constructions.PolynomialSeparation.homogeneous_equations (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone _)
    (Torus.TorusAlgebraicPeriodCone.CM.Algebraization.AlgebraicPeriodCone.separating_polynomial Φ f hf hd L hker hsurj)

theorem smooth_integral_model :
    ∃ e : Φ.periodTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver (range f)),
      IsIntegral (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) ∧ Smooth (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureOver (range f)).hom ∧
      (∀ t, e t = Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap f t) ∧
      ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.inclusionOver (range f)) (e t) =
        AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n (f t) := by
  obtain ⟨Q, hQ, hcone⟩ := homogeneous_equations Φ f hf hd
  have hS (w) (hw : ∀ p ∈ MvPolynomial.vanishingIdeal ℂ (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)),
      MvPolynomial.eval w p = 0) : w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    rw [hcone]
    intro p hp
    apply hw p
    intro v hv
    rw [hcone] at hv
    exact hv p hp
  have hsm := fun i => Torus.TorusPeriodChartAlgebra.CM.Algebraization.PeriodChartAlgebra.smooth Φ f hf hd hS i
  have hsurj := Geometry.ComplexTorus.RiemannProjectivity.ExactProjective.Constructions.ExactProjectiveClosure.liftedMap_surjective f Q hQ hcone
  let e := (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_isClosedEmbedding f hf).isEmbedding.toHomeomorphOfSurjective hsurj
  have hint : IsIntegral (Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.closureScheme (range f)) :=
    Torus.TorusProjectiveIrreducibility.CM.Algebraization.ProjectiveIrreducibility.closureScheme_integral_of_torus_embedding _ f hf.continuous (by
      intro z
      obtain ⟨i, hi⟩ := AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (f (QuotientAddGroup.mk z))
      exact ⟨i, hi, Torus.ProjectiveModel.CM.Algebraization.ProjectiveTorusModel.coordinates_differentiableAt
        (hf.continuous.comp QuotientAddGroup.continuous_mk).continuousAt i hi (hd z i hi).1⟩)
  exact ⟨e, hint, Torus.SmoothProjectiveModel.CM.Algebraization.SmoothProjectiveTorusModel.smooth_closure Q hQ hcone hsm,
    fun _ => rfl, Geometry.ComplexTorus.RiemannProjectivity.ProjectiveClosureIs.Constructions.ProjectiveClosure.liftedMap_inclusion f⟩

end

end OAI.RepresentationTheory.Theta.Geometric.ChosenProjective.CM.Torus.Algebraization.ChosenProjectiveModel
