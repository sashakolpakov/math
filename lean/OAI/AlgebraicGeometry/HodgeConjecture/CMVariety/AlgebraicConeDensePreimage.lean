import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicFiniteConeFibers
import OAI.Geometry.ComplexTorus.RiemannProjectivity.DenseFiber

/-! # Algebraic Cone Dense Preimage -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeDensePreimage.CM.Abelian.Algebraization.ConeParameterFibers

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem parameterization_injOn (i : Fin (n + 1))
    {g : V → Projectivization ℂ (Fin (n + 1) → ℂ)} {U : Set V}
    (hg : InjOn g U) (hchart : ∀ z ∈ U, g z ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) :
    InjOn (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i (fun z => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z)))
      (U ×ˢ {c : ℂ | c ≠ 0}) := by
  intro p hp q hq heq
  have hsnd : p.2 = q.2 := by
    simpa only [Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization, Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.insertCoordinate_apply, Fin.insertNth_apply_same]
      using congrFun heq i
  have hr : ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g p.1) = ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g q.1) := by
    have h := congrArg (ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i) heq
    simpa only [Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.dehomogenize_parameterization i _ _ hp.2,
      Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.dehomogenize_parameterization i _ _ hq.2] using h
  exact Prod.ext (hg hp.1 hq.1 ((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).injOn
    (hchart p.1 hp.1) (hchart q.1 hq.1) hr)) hsnd

theorem exists_injective_period_parameter (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsEmbedding f)
    (i : Fin (n + 1)) (z : Φ.space)
    (hi : f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source) {c : ℂ} (hc : c ≠ 0) :
    ∃ U : Set (Φ.space × ℂ), IsOpen U ∧ (z, c) ∈ U ∧
      InjOn (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w)))) U ∧
      ∀ p ∈ U, f (QuotientAddGroup.mk p.1) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source ∧ p.2 ≠ 0 := by
  obtain ⟨A, hA, hzA, hq⟩ :=
    Φ.periodProjection_isCoveringMap.isLocalHomeomorph.isLocallyInjective z
  let B := A ∩ (fun w : Φ.space => f (QuotientAddGroup.mk w)) ⁻¹'
    (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
  have hB : IsOpen B := hA.inter ((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage
    (hf.continuous.comp QuotientAddGroup.continuous_mk))
  have hg : InjOn (fun w : Φ.space => f (QuotientAddGroup.mk w)) B :=
    fun _ hp _ hq' heq => hq hp.1 hq'.1 (hf.injective heq)
  refine ⟨B ×ˢ {c : ℂ | c ≠ 0}, hB.prod isOpen_compl_singleton, ⟨⟨hzA, hi⟩, hc⟩,
    parameterization_injOn i hg (fun _ hw => hw.2), fun p hp => ⟨hp.1.2, hp.2⟩⟩

theorem finite_parameter_fiber {D W : Type*} {S : Set W} {P : D → W} {U : Set D}
    (hP : InjOn P U) (hmem : MapsTo P U S) {Y : Type*} (L : W → Y)
    (hfinite : ∀ y, {w : W | w ∈ S ∧ L w = y}.Finite) (y : Y) :
    {x : D | x ∈ U ∧ L (P x) = y}.Finite := by
  apply Set.Finite.of_finite_image (f := P) (h := (hfinite y).subset ?_)
  · exact hP.mono (fun _ hx => hx.1)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨hmem hx.1, hx.2⟩

end AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeDensePreimage.CM.Abelian.Algebraization.ConeParameterFibers

namespace AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeDensePreimage.CM.Abelian.Algebraization.ConeDensePreimage

open Set
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeDensePreimage.CM.Abelian.Algebraization.ConeParameterFibers

variable {n : ℕ}

theorem parameter_mem_closure (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ))
    (hfinite : ∀ y, {w | w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L w = y}.Finite)
    (i : Fin (n + 1)) (z : Φ.space) {c : ℂ} (hc : c ≠ 0)
    (hi : f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    {O D : Set (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)}
    (hO : IsOpen O) (hD : O ⊆ closure D)
    (hbase : L (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i
      (f (QuotientAddGroup.mk w))) (z, c)) ∈ O) :
    Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, c) ∈
      closure {w | w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L w ∈ D} := by
  let r : Φ.space → Fin n → ℂ :=
    fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))
  let P := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i r
  let F := fun p => L (P p)
  obtain ⟨A, hA, hzA, hPinj, hpatch⟩ := ConeParameterFibers.exists_injective_period_parameter Φ f hf i z hi hc
  have hr : DifferentiableOn ℂ r
      {w | f (QuotientAddGroup.mk w) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source} :=
    fun w hw => (hd w i hw).differentiableWithinAt
  have hP : DifferentiableOn ℂ P A :=
    (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.differentiableOn_parameterization i hr).mono (fun p hp => ⟨(hpatch p hp).1, mem_univ _⟩)
  have hF : DifferentiableOn ℂ F A := L.differentiable.comp_differentiableOn hP
  have hmem : MapsTo P A (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) := by
    intro p hp hp0
    obtain ⟨w, hw⟩ := (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization_mem_cone i
      (fun w : Φ.space => f (QuotientAddGroup.mk w)) p.1 (hpatch p hp).1 p.2) hp0
    exact ⟨QuotientAddGroup.mk w, hw⟩
  let U := A ∩ F ⁻¹' O
  have hU : IsOpen U := hF.continuousOn.isOpen_inter_preimage hA hO
  have hzU : (z, c) ∈ U := ⟨hzA, hbase⟩
  have hfin : ∀ y, {p : Φ.space × ℂ | p ∈ U ∧ F p = y}.Finite :=
    fun y => ConeParameterFibers.finite_parameter_fiber (hPinj.mono inter_subset_left)
      (hmem.mono_left inter_subset_left) L hfinite y
  have hdense := Geometry.ComplexTorus.RiemannProjectivity.DenseFiber.Constructions.DenseFiberPreimage.dense_preimage hU (hF.mono inter_subset_left)
    (by simp [Module.finrank_prod]) hfin (fun p hp => hD hp.2)
  have hclosure := mem_closure_image
    ((hP.differentiableAt (hA.mem_nhds hzA)).continuousAt) (hdense hzU)
  apply closure_mono (s := P '' (U ∩ F ⁻¹' D)) ?_ hclosure
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨hmem hp.1.1, hp.2⟩

theorem mem_closure_preimage (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)) (hf : Topology.IsEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ))
    (hfinite : ∀ y, {w | w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L w = y}.Finite)
    {O D : Set (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)}
    (hO : IsOpen O) (hD : O ⊆ closure D)
    {v : Fin (n + 1) → ℂ} (hv : v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) (hv0 : v ≠ 0)
    (hbase : L v ∈ O) : v ∈ closure {w | w ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L w ∈ D} := by
  obtain ⟨t, ht⟩ := hv hv0
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective t
  have hgz : f (QuotientAddGroup.mk z) = Projectivization.mk ℂ v hv0 := by rw [hz, ht]
  obtain ⟨i, hpatch⟩ := ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (Projectivization.mk ℂ v hv0)
  have hi : f (QuotientAddGroup.mk z) ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source := by rwa [hgz]
  have hvi : v i ≠ 0 := (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv0).mp hpatch
  have hratio : ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk z)) = ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize i v := by
    rw [hgz, ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize_eq_projectiveChart i v hv0]
  have hparam : Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i
      (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, v i) = v := by
    change Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.insertCoordinate i (v i, v i • ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk z))) = v
    rw [hratio]
    exact Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.insertCoordinate_dehomogenize i v hvi
  have h := parameter_mem_closure Φ f hf hd L hfinite i z hvi hi hO hD
    (by rw [hparam]; exact hbase)
  simpa only [hparam] using h

end AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeDensePreimage.CM.Abelian.Algebraization.ConeDensePreimage

end

end OAI
