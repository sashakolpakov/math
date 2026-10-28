import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Quotient
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus

/-! # Continuous Analytic Removable -/

namespace OAI.RepresentationTheory.Theta.Geometric.ContinuousAnalyticRemovable

noncomputable section

/-! A continuous function holomorphic outside a locally analytic set is
holomorphic at a point where that set contains no neighborhood. -/

set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped _root_.Topology

theorem continuous_differentiableAt_of_analytic_exception {n : ℕ}
    {f : (Fin n → ℂ) → ℂ} {U S : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hd : ∀ y ∈ U, y ∉ S → DifferentiableAt ℂ f y)
    {x : Fin n → ℂ} (hx : x ∈ U) (hS : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S x)
    (hn : S ∉ 𝓝 x) : DifferentiableAt ℂ f x := by
  obtain ⟨V, hV, hxV, m, g, hg, heq⟩ := hS
  have hex : ∃ i : Fin m, ¬∀ᶠ y in 𝓝 x, g i y = 0 := by
    by_contra h
    have hzero : ∀ i : Fin m, ∀ᶠ y in 𝓝 x, g i y = 0 := by simpa only [not_exists, not_not] using h
    apply hn
    filter_upwards [hV.mem_nhds hxV, Filter.eventually_all.mpr hzero] with y hy hgy
    exact (heq y hy).mpr hgy
  obtain ⟨i, hi⟩ := hex
  let B := U ∩ {y | ‖f y‖ < ‖f x‖ + 1}
  have hB : IsOpen B := hf.norm.isOpen_inter_preimage hU isOpen_Iio
  have hxB : x ∈ B := by
    refine ⟨hx, ?_⟩
    change ‖f x‖ < ‖f x‖ + 1
    linarith
  let W := V ∩ B
  have hW : IsOpen W := hV.inter hB
  have hxW : x ∈ W := ⟨hxV, hxB⟩
  obtain ⟨D, hD, hxD, hDW, hdense⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree.Constructions.GenericPolynomial.exists_dense_nonzero_neighborhood hW hxW
    ((hg i).mono inter_subset_left) hi
  have hDV : D ⊆ V := fun _ hy => (hDW hy).1
  have hDU : D ⊆ U := fun _ hy => (hDW hy).2.1
  have hgood : DifferentiableOn ℂ f {y | y ∈ D ∧ g i y ≠ 0} := by
    intro y hy
    apply (hd y (hDU hy.1) ?_).differentiableWithinAt
    intro hyS
    exact hy.2 ((heq y (hDV hy.1)).mp hyS i)
  obtain ⟨O, F, hO, hxO, hOD, hF, hFeq⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Quotient.Constructions.Removable.exists_extension_off_zero_set hD
    ((hg i).mono hDV) hgood hxD hi ⟨‖f x‖ + 1, fun y hy _ => (hDW hy).2.2.le⟩
  have hequal : EqOn F f O := by
    intro z hz
    have hfreq : ∃ᶠ y in 𝓝 z, F y = f y :=
      ((mem_closure_iff_frequently.mp (hdense (hOD hz))).and_eventually (hO.mem_nhds hz)).mono
        (fun y hy => hFeq y hy.2 hy.1.2)
    exact tendsto_nhds_unique_of_frequently_eq
      (hF.differentiableAt (hO.mem_nhds hz)).continuousAt
      (hf.continuousAt (hU.mem_nhds (hDU (hOD hz)))) hfreq
  apply (hF.differentiableAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact (hequal hy).symm

end

end OAI.RepresentationTheory.Theta.Geometric.ContinuousAnalyticRemovable
