import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialImplicit
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Local Graph Chart -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalGraphChart

noncomputable section

/-!
# Genuine local charts from analytic polynomial graphs

The chart domain is the actual subtype cut out by polynomial evaluation in
ordinary complex coordinate space. Local graph existence and uniqueness give
an open partial homeomorphism with coordinate projection as its forward map.
The inverse, regarded in the ambient coordinate space, is complex analytic.

This construction is local at a point where the specified partial derivative
is invertible. It does not assume or assert a comparison with scheme smoothness.
-/

open Filter Set
open scoped _root_.Topology ContDiff

section LocalGraph

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- A local graph supplies a coordinate chart on the actual subset. The default
point is used only to give the inverse a value outside its open target. -/
def localGraphChart (S : Set (E × F)) (z₀ : S) (ψ : E → F)
    (U : Set E) (W : Set (E × F))
    (hU : IsOpen U) (hW : IsOpen W) (hψ : ContinuousOn ψ U)
    (hzero : ∀ x ∈ U, (x, ψ x) ∈ S)
    (hgraph : ∀ x ∈ U, (x, ψ x) ∈ W)
    (hunique : ∀ z ∈ W, z ∈ S → ψ z.1 = z.2) :
    OpenPartialHomeomorph S E := by
  classical
  exact
    { toFun := fun z => z.val.1
      invFun := fun x => if hx : x ∈ U then ⟨(x, ψ x), hzero x hx⟩ else z₀
      source := {z : S | z.val ∈ W ∧ z.val.1 ∈ U}
      target := U
      map_source' := fun _ hz => hz.2
      map_target' := by
        intro x hx
        simp only [dite_eq_left hx, Set.mem_ofPred_eq]
        exact ⟨hgraph x hx, hx⟩
      left_inv' := by
        intro z hz
        apply Subtype.ext
        simp only [dite_eq_left hz.2]
        exact Prod.ext rfl (hunique z.val hz.1 z.property)
      right_inv' := by
        intro x hx
        simp only [dite_eq_left hx]
      open_source :=
        (hW.preimage continuous_subtype_val).inter
          (hU.preimage (continuous_fst.comp continuous_subtype_val))
      open_target := hU
      continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
      continuousOn_invFun := by
        apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        apply (continuousOn_id.prodMk hψ).congr
        intro x hx
        simp only [Function.comp_apply, dite_eq_left hx, id_eq] }

end LocalGraph

/-- At a regular point of an actual polynomial zero set, coordinate projection
is a local homeomorphism and its inverse is complex analytic in ambient space. -/
theorem exists_polynomial_zero_chart
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : κ → MvPolynomial (ι ⊕ κ) ℂ)
    (u : (ι → ℂ) × (κ → ℂ))
    (hu : PolynomialImplicit.splitPolynomialMap P u = 0)
    (hreg : (fderiv ℂ (PolynomialImplicit.splitPolynomialMap P) u ∘L
      ContinuousLinearMap.inr ℂ (ι → ℂ) (κ → ℂ)).IsInvertible) :
    ∃ e : OpenPartialHomeomorph {z | PolynomialImplicit.splitPolynomialMap P z = 0} (ι → ℂ),
      (⟨u, hu⟩ : {z | PolynomialImplicit.splitPolynomialMap P z = 0}) ∈ e.source ∧
      (∀ z, e z = z.val.1) ∧
      ContDiffOn ℂ ω (fun x => (e.symm x).val) e.target := by
  classical
  obtain ⟨ψ, hψu, hψdiff, hzeroNear, huniqueNear⟩ :=
    PolynomialImplicit.exists_polynomial_zero_graph P u hu hreg
  obtain ⟨W, hWsub, hWopen, huW⟩ := mem_nhds_iff.mp huniqueNear
  have hbaseW : (u.1, ψ u.1) ∈ W := by
    simpa only [hψu, Prod.mk.eta] using huW
  have hgraphContinuous : ContinuousAt (fun x => (x, ψ x)) u.1 :=
    continuousAt_id.prodMk hψdiff.continuousAt
  have hgraphNear : ∀ᶠ x in 𝓝 u.1, (x, ψ x) ∈ W :=
    hgraphContinuous.preimage_mem_nhds (hWopen.mem_nhds hbaseW)
  have hdiffNear : ∀ᶠ x in 𝓝 u.1, ContDiffAt ℂ ω ψ x :=
    hψdiff.eventually (by simp)
  obtain ⟨U, hUsub, hUopen, huU⟩ :=
    mem_nhds_iff.mp (hzeroNear.and (hgraphNear.and hdiffNear))
  have hψOn : ContDiffOn ℂ ω ψ U :=
    fun x hx => (hUsub hx).2.2.contDiffWithinAt
  let e := localGraphChart {z | PolynomialImplicit.splitPolynomialMap P z = 0} ⟨u, hu⟩ ψ U W
    hUopen hWopen hψOn.continuousOn
    (fun x hx => (hUsub hx).1)
    (fun x hx => (hUsub hx).2.1)
    (fun z hz hzero => (hWsub hz).mp hzero)
  refine ⟨e, ?_, ?_, ?_⟩
  · exact ⟨huW, huU⟩
  · intro z
    rfl
  · change ContDiffOn ℂ ω (fun x => (e.symm x).val) U
    apply (contDiffOn_id.prodMk hψOn).congr
    intro x hx
    change (if h : x ∈ U then
      (⟨(x, ψ x), (hUsub h).1⟩ : {z | PolynomialImplicit.splitPolynomialMap P z = 0})
      else ⟨u, hu⟩).val = (id x, ψ x)
    rw [dite_eq_left hx]
    rfl

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalGraphChart
