import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticElimination
import Mathlib.Topology.Maps.Proper.Basic

/-! # Proper Analytic Image -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity

noncomputable section

/-!
# Proper projection of an analytic set with finite fibers

Finitely many local disk projections cover the fiber. Properness makes this
cover valid over a neighborhood in the base, and finite unions preserve
local holomorphic equations.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology BigOperators

theorem ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt.finite_iUnion
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    {S : ι → Set E} {x : E} (hlocal : ∀ i, ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (S i) x) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (⋃ i, S i) x := by
  classical
  choose U hU hx m f hf heq using hlocal
  let V := ⋂ i, U i
  have hV : IsOpen V := isOpen_iInter_of_finite hU
  have hxV : x ∈ V := mem_iInter.mpr hx
  let I := (i : ι) → Fin (m i)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let g : Fin (Fintype.card I) → E → ℂ := fun k y => ∏ i, f i (e.symm k i) y
  refine ⟨V, hV, hxV, Fintype.card I, g, ?_, ?_⟩
  · intro k
    exact AnalyticElimination.Constructions.Elimination.differentiableOn_finset_product Finset.univ
      (fun i _ => (hf i (e.symm k i)).mono (iInter_subset U i))
  · intro y hy
    constructor
    · intro h k
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      have hfi := (heq i y (mem_iInter.mp hy i)).mp hi
      exact Finset.prod_eq_zero_iff.mpr ⟨i, Finset.mem_univ _, hfi (e.symm k i)⟩
    · intro h
      by_contra hyS
      have hn : ∀ i, ∃ j : Fin (m i), f i j y ≠ 0 := by
        intro i
        have hi : y ∉ S i := fun hi => hyS (mem_iUnion.mpr ⟨i, hi⟩)
        simpa only [not_forall] using (not_congr (heq i y (mem_iInter.mp hy i))).mp hi
      choose j hj using hn
      have hz := h (e j)
      change (∏ i, f i (e.symm (e j) i) y) = 0 at hz
      rw [e.symm_apply_apply] at hz
      exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)) hz

/-- Properness and finiteness globalize the local elimination theorem.
Only points of the fiber over `x` require local analytic equations here. -/
theorem ProperAnalyticImage.Constructions.Cone.holomorphicZeroSetAt_proper_projection {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ z, (x, z) ∈ S → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, z)) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt {y | ∃ z, (y, z) ∈ S} x := by
  classical
  let K := {z : ℂ | (x, z) ∈ S}
  let : Fintype K := hfinite.fintype
  have hdisks : ∀ a : K, ∃ R : ℝ, 0 < R ∧
      ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt {y | ∃ z ∈ closedBall (a : ℂ) R, (y, z) ∈ S} x :=
    fun a => AnalyticElimination.Constructions.Elimination.holomorphic_local_projection (hlocal a a.property) hfinite
  choose R hR hanalytic using hdisks
  let A : K → Set (Fin n → ℂ) := fun a => {y | ∃ z ∈ closedBall (a : ℂ) (R a), (y, z) ∈ S}
  have hA : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (⋃ a, A a) x := ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt.finite_iUnion hanalytic
  let O : Set ((Fin n → ℂ) × ℂ) := ⋃ a : K, Prod.snd ⁻¹' ball (a : ℂ) (R a)
  have hO : IsOpen O := isOpen_iUnion (fun a => isOpen_ball.preimage continuous_snd)
  let D : Set S := Subtype.val ⁻¹' Oᶜ
  have hD : IsClosed D := hO.isClosed_compl.preimage continuous_subtype_val
  have hclosed : IsClosed ((fun p : S => p.val.1) '' D) := hproper.isClosedMap D hD
  have hxnot : x ∉ (fun p : S => p.val.1) '' D := by
    rintro ⟨⟨⟨y, z⟩, hyz⟩, hpD, hpx⟩
    dsimp only at hpx
    subst y
    have hzK : z ∈ K := hyz
    apply hpD
    exact mem_iUnion.mpr ⟨⟨z, hzK⟩, mem_ball_self (hR ⟨z, hzK⟩)⟩
  apply hA.congr
  filter_upwards [hclosed.isOpen_compl.mem_nhds hxnot] with y hy
  constructor
  · rintro ⟨z, hyz⟩
    have hyo : (y, z) ∈ O := by
      by_contra hnot
      exact hy ⟨⟨(y, z), hyz⟩, hnot, rfl⟩
    obtain ⟨a, ha⟩ := mem_iUnion.mp hyo
    exact mem_iUnion.mpr ⟨a, z, ball_subset_closedBall ha, hyz⟩
  · intro h
    obtain ⟨a, z, _, hzs⟩ := mem_iUnion.mp h
    exact ⟨z, hzs⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity
