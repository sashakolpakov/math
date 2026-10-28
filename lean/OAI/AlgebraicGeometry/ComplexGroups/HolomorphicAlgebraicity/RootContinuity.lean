import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ContourRemainderAt

/-! # Root Continuity -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootContinuity.Constructions.RootPolynomials

noncomputable section

/-!
# Persistence of roots of monic polynomial families

If all roots were at distance at least `r` from a point, the product formula
would give an evaluation of norm at least `r ^ degree`. This proves root
persistence directly from continuity of the coefficients.
-/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology

theorem norm_eval_eq_prod_norm_roots {P : ℂ[X]} (hP : P.Monic) (z : ℂ) :
    ‖P.eval z‖ = (P.roots.map (fun w => ‖z - w‖)).prod := by
  rw [(IsAlgClosed.splits P).eval_eq_prod_roots_of_monic hP]
  change (normHom.toMonoidHom : ℂ →* ℝ) (P.roots.map (fun w => z - w)).prod = _
  rw [map_multiset_prod, Multiset.map_map]
  rfl

theorem exists_root_near_of_eval_lt {P : ℂ[X]} (hP : P.Monic)
    {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hsmall : ‖P.eval z‖ < r ^ P.natDegree) :
    ∃ w ∈ ball z r, P.eval w = 0 := by
  by_contra hn
  have hdist (w : ℂ) (hw : w ∈ P.roots) : r ≤ ‖z - w‖ := by
    by_contra hnot
    apply hn
    refine ⟨w, ?_, (mem_roots hP.ne_zero).mp hw⟩
    rw [mem_ball_iff_norm, norm_sub_rev]
    exact lt_of_not_ge hnot
  have hprod : r ^ P.natDegree ≤ ‖P.eval z‖ := by
    rw [norm_eval_eq_prod_norm_roots hP, (IsAlgClosed.splits P).natDegree_eq_card_roots]
    calc
      _ = (P.roots.map (Function.const ℂ r)).prod := by rw [Multiset.map_const, Multiset.prod_replicate]
      _ ≤ _ := Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ => hr) hdist
  exact (not_lt_of_ge hprod) hsmall

theorem eventually_root_near {n d : ℕ} {P : (Fin n → ℂ) → ℂ[X]}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U)
    (hP : ∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d)
    {x : Fin n → ℂ} (hx : x ∈ U) {z : ℂ} (hz : (P x).eval z = 0)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ y in 𝓝 x, ∃ w ∈ ball z r, (P y).eval w = 0 := by
  have hdiff := ContourRemainderAt.Constructions.ContourRemainder.differentiableOn_polynomial_eval hcoeff
    (fun y hy => (hP y hy).2.le)
  have hcont : ContinuousAt (fun y => (P y).eval z) x := by
    exact (hdiff.differentiableAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z⟩)).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)
  have hsmall : ∀ᶠ y in 𝓝 x, ‖(P y).eval z‖ < r ^ d :=
    hcont.norm.eventually (gt_mem_nhds (by
      change ‖(P x).eval z‖ < r ^ d
      rw [hz, norm_zero]
      exact pow_pos hr d))
  filter_upwards [hU.mem_nhds hx, hsmall] with y hy hys
  apply exists_root_near_of_eval_lt (hP y hy).1 hr.le
  simpa only [(hP y hy).2] using hys

theorem root_mem_closed_set_of_generic_roots {n d : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} (hS : IsClosed S)
    {P : (Fin n → ℂ) → ℂ[X]} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U)
    (hP : ∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d)
    {G : Set (Fin n → ℂ)} (hdense : U ⊆ closure G)
    (hroot : ∀ y ∈ G, ∀ z : ℂ, (P y).eval z = 0 → (y, z) ∈ S)
    {x : Fin n → ℂ} (hx : x ∈ U) {z : ℂ} (hz : (P x).eval z = 0) :
    (x, z) ∈ S := by
  rw [← hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro r hr
  have hnear := eventually_root_near hU hcoeff hP hx hz hr
  obtain ⟨y, hyG, hyroot, hyball⟩ := ((mem_closure_iff_frequently.mp (hdense hx)).and_eventually
    (hnear.and (ball_mem_nhds x hr))).exists
  obtain ⟨w, hwball, hwroot⟩ := hyroot
  refine ⟨(y, w), hroot y hyG w hwroot, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨by simpa only [dist_comm] using mem_ball.mp hyball,
    by simpa only [dist_comm] using mem_ball.mp hwball⟩

theorem eval_eq_zero_of_generic_roots_of_open_projection {n d : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} (hopen : IsOpenMap (fun p : S => p.val.1))
    {P : (Fin n → ℂ) → ℂ[X]} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d)
    {G : Set (Fin n → ℂ)} (hdense : U ⊆ closure G)
    (hroot : ∀ y ∈ G, ∀ z : ℂ, (y, z) ∈ S → (P y).eval z = 0)
    {x : Fin n → ℂ} (hx : x ∈ U) {z : ℂ} (hz : (x, z) ∈ S) :
    (P x).eval z = 0 := by
  let p : S := ⟨(x, z), hz⟩
  have hclosure : p ∈ closure ((fun q : S => q.val.1) ⁻¹' G) :=
    hopen.preimage_closure_subset_closure_preimage (hdense hx)
  have hdiff := ContourRemainderAt.Constructions.ContourRemainder.differentiableOn_polynomial_eval hcoeff hdegree
  have hcont : ContinuousAt (fun q : S => (P q.val.1).eval q.val.2) p :=
    (hdiff.differentiableAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z⟩)).continuousAt.comp
      continuous_subtype_val.continuousAt
  apply tendsto_nhds_unique_of_frequently_eq hcont.tendsto tendsto_const_nhds
  apply (mem_closure_iff_frequently.mp hclosure).mono
  intro q hq
  exact hroot q.val.1 hq q.val.2 q.property

theorem full_fiber_eq_of_open_projection {n d : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} (hS : IsClosed S)
    (hopen : IsOpenMap (fun p : S => p.val.1))
    {P : (Fin n → ℂ) → ℂ[X]} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U)
    (hP : ∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d)
    {G : Set (Fin n → ℂ)} (hdense : U ⊆ closure G)
    (hroot : ∀ y ∈ G, ∀ z : ℂ, (y, z) ∈ S ↔ (P y).eval z = 0)
    {x : Fin n → ℂ} (hx : x ∈ U) (z : ℂ) :
    (x, z) ∈ S ↔ (P x).eval z = 0 := by
  constructor
  · exact eval_eq_zero_of_generic_roots_of_open_projection hopen hU hcoeff
      (fun y hy => (hP y hy).2.le) hdense (fun y hy z => (hroot y hy z).mp) hx
  · exact root_mem_closed_set_of_generic_roots hS hU hcoeff hP hdense
      (fun y hy z => (hroot y hy z).mpr) hx

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootContinuity.Constructions.RootPolynomials
