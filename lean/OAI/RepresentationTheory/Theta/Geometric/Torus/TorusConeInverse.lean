import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF
import OAI.Geometry.ComplexTorus.RiemannProjectivity.BranchCoefficientsAt

/-! # Torus Cone Inverse -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConeInverse.CM.Algebraization.ConeInverse

noncomputable section

open Set Filter
open scoped _root_.Topology

variable {D V W : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem inverse_on_embedded_image {S : Set V} (f : S → W) (hf : Continuous f)
    (P : D → V) (q : OpenPartialHomeomorph D W)
    (hP : DifferentiableOn ℂ P q.source) (hqi : DifferentiableOn ℂ q.symm q.target)
    (hmem : ∀ x ∈ q.source, P x ∈ S)
    (hcomp : ∀ x (hx : x ∈ q.source), f ⟨P x, hmem x hx⟩ = q x)
    (v₀ : S)
    (hcover : {v : S | ∃ x ∈ q.source, P x = v.val} ∈ 𝓝 v₀) :
    Geometry.ComplexTorus.RiemannProjectivity.BranchCoefficientsAt.Constructions.BranchCoefficients.HasHolomorphicInverseAt (Subtype.val : S → V) f v₀ := by
  classical
  let s : W → S := fun y => if hy : y ∈ q.target then
    ⟨P (q.symm y), hmem _ (q.map_target hy)⟩ else v₀
  have hsval (y : W) (hy : y ∈ q.target) : (s y).val = P (q.symm y) := by simp [s, hy]
  have hscont : ContinuousOn s q.target := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (hP.continuousOn.comp q.continuousOn_symm q.mapsTo_symm).congr
      (fun y hy => hsval y hy)
  have hright (y : W) (hy : y ∈ q.target) : f (s y) = y := by
    dsimp [s]
    rw [dite_eq_left hy, hcomp _ (q.map_target hy), q.right_inv hy]
  obtain ⟨O, hOC, hO, hvO⟩ := mem_nhds_iff.mp hcover
  have hleft (v : S) (hv : v ∈ O) : s (f v) = v ∧ f v ∈ q.target := by
    obtain ⟨x, hx, hPx⟩ := hOC hv
    have hPv : (⟨P x, hmem x hx⟩ : S) = v := Subtype.ext hPx
    have hfx : f v = q x := by rw [← hPv]; exact hcomp x hx
    refine ⟨?_, hfx ▸ q.map_source hx⟩
    apply Subtype.ext
    rw [hsval _ (hfx ▸ q.map_source hx), hfx, q.left_inv hx, hPx]
  let U := q.target ∩ s ⁻¹' O
  have hU : IsOpen U := hscont.isOpen_inter_preimage q.open_target hO
  let e : OpenPartialHomeomorph S W :=
    { toFun := f
      invFun := s
      source := O
      target := U
      map_source' := fun v hv => ⟨(hleft v hv).2, by
        change s (f v) ∈ O
        rw [(hleft v hv).1]
        exact hv⟩
      map_target' := fun y hy => hy.2
      left_inv' := fun v hv => (hleft v hv).1
      right_inv' := fun y hy => hright y hy.1
      open_source := hO
      open_target := hU
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hscont.mono inter_subset_left }
  refine ⟨e, hvO, rfl, ?_⟩
  change DifferentiableOn ℂ (fun y => (s y).val) U
  apply ((hP.comp hqi q.mapsTo_symm).mono inter_subset_left).congr
  intro y hy
  exact hsval y hy.1

open OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent

/-- A regular point of a period-cone parameter chart is a genuine
holomorphic local inverse point of the projection on the cone. -/
theorem holomorphic_inverse_of_regular_period_parameter {n k : ℕ}
    (Φ : Data.CM.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Topology.IsEmbedding f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      DifferentiableAt ℂ (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z)
    (L : (Fin (n + 1) → ℂ) →L[ℂ] (Fin k → ℂ))
    (i : Fin (n + 1)) (z : Φ.space) (c : ℂ) (hc : c ≠ 0)
    (hi : f (QuotientAddGroup.mk z) ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source)
    (v₀ : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
    (hv₀ : v₀.val = Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i
      (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) (z, c))
    (hreg : Function.Bijective (fderiv ℂ (fun p => L (Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i
      (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) p)) (z, c))) :
    Geometry.ComplexTorus.RiemannProjectivity.BranchCoefficientsAt.Constructions.BranchCoefficients.HasHolomorphicInverseAt
      (Subtype.val : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → (Fin (n + 1) → ℂ))
      (fun v => L v) v₀ := by
  let g : Φ.space → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun w => f (QuotientAddGroup.mk w)
  let r : Φ.space → Fin n → ℂ := fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g w)
  let U := g ⁻¹' (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
  let P := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization i r
  have hU : IsOpen U := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage
    (hf.continuous.comp QuotientAddGroup.continuous_mk)
  have hr : DifferentiableOn ℂ r U := fun w hw => (hd w i hw).differentiableWithinAt
  have hP : DifferentiableOn ℂ P (U ×ˢ univ) := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.differentiableOn_parameterization i hr
  have hF : DifferentiableOn ℂ (fun w => L (P w)) (U ×ˢ univ) :=
    L.differentiable.comp_differentiableOn hP
  have hx : (z, c) ∈ U ×ˢ univ := ⟨hi, mem_univ _⟩
  obtain ⟨q, hq, hqF, hqi⟩ := Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt.Constructions.FiniteBranches.holomorphic_local_inverse
    (hU.prod isOpen_univ) hF hx hreg
  let q' := q.restrOpen (U ×ˢ univ) (hU.prod isOpen_univ)
  have hxq' : (z, c) ∈ q'.source := ⟨hq, hx⟩
  have hmem : ∀ w ∈ q'.source, P w ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) := by
    intro w hw hv0
    have h := Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeTangent.parameterization_mem_cone i g w.1 hw.2.1 w.2 hv0
    obtain ⟨u, hu⟩ := h
    exact ⟨QuotientAddGroup.mk u, hu⟩
  apply inverse_on_embedded_image (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v)
    (L.continuous.comp continuous_subtype_val) P q' (hP.mono inter_subset_right)
    (hqi.mono inter_subset_left) hmem
    (fun w _ => (congrFun hqF w).symm) v₀
  exact Geometry.ComplexTorus.RiemannProjectivity.ConeTangentF.Constructions.ConeLocalTopology.parameter_image_mem_nhds
    (QuotientAddGroup.mk : Φ.space → Φ.periodTorus) QuotientAddGroup.isOpenMap_coe
    f hf i z c hc hi v₀ hv₀ (q'.open_source.mem_nhds hxq')

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConeInverse.CM.Algebraization.ConeInverse
