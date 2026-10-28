import OAI.Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot
import Mathlib.Analysis.Normed.Field.Approximation

/-! # Root Continuity At -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.RootContinuityAt.Constructions.RootContinuity

/-! # RiemannProjectivity: roots of a continuous monic family persist locally -/

open Set Filter _root_.Polynomial _root_.Metric
open scoped _root_.Topology BigOperators

theorem exists_root_near_of_eval_small {p : ℂ[X]} (hp : p.Monic) {z : ℂ} {ε : ℝ}
    (hε : 0 < ε) (heval : ‖p.eval z‖ < ε ^ p.natDegree) :
    ∃ w, p.eval w = 0 ∧ dist z w < ε := by
  by_contra! hn
  have hle := Multiset.prod_map_le_prod_map₀ (s := p.roots)
    (fun _ : ℂ => ε) (fun w => ‖z - w‖) (fun _ _ => hε.le)
    (fun w hw => by simpa only [dist_eq_norm] using hn w ((mem_roots hp.ne_zero).mp hw))
  have hprod : (p.roots.map (fun w => ‖z - w‖)).prod = ‖p.eval z‖ := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp]
    exact (p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun w => z - w))
  rw [hprod, Multiset.map_const', Multiset.prod_replicate,
    ← (IsAlgClosed.splits p).natDegree_eq_card_roots] at hle
  exact heval.not_ge hle

theorem continuousAt_eval {V : Type*} [TopologicalSpace V] {P : V → ℂ[X]} {x : V}
    (d : ℕ) (hd : ∀ y, (P y).natDegree ≤ d)
    (hcoeff : ∀ j, ContinuousAt (fun y => (P y).coeff j) x) (z : ℂ) :
    ContinuousAt (fun y => (P y).eval z) x := by
  have heq : (fun y => (P y).eval z) =
      fun y => ∑ j ∈ Finset.range (d + 1), (P y).coeff j * z ^ j := by
    funext y
    exact eval_eq_sum_range' (Nat.lt_succ_of_le (hd y)) z
  rw [heq]
  exact tendsto_finsetSum _ (fun j _ => (hcoeff j).mul continuousAt_const)

theorem continuousAt_eval_pair {V : Type*} [TopologicalSpace V] {P : V → ℂ[X]} {x : V}
    (d : ℕ) (hd : ∀ y, (P y).natDegree ≤ d)
    (hcoeff : ∀ j, ContinuousAt (fun y => (P y).coeff j) x) (z : ℂ) :
    ContinuousAt (fun p : V × ℂ => (P p.1).eval p.2) (x, z) := by
  have heq : (fun p : V × ℂ => (P p.1).eval p.2) =
      fun p => ∑ j ∈ Finset.range (d + 1), (P p.1).coeff j * p.2 ^ j := by
    funext p
    exact eval_eq_sum_range' (Nat.lt_succ_of_le (hd p.1)) p.2
  rw [heq]
  have hf : ContinuousAt (Prod.fst : V × ℂ → V) (x, z) := continuous_fst.continuousAt
  have hs : ContinuousAt (Prod.snd : V × ℂ → ℂ) (x, z) := continuous_snd.continuousAt
  apply tendsto_finsetSum
  intro j _
  have hcj : ContinuousAt (fun p : V × ℂ => (P p.1).coeff j) (x, z) :=
    ContinuousAt.comp' (f := Prod.fst) (g := fun y : V => (P y).coeff j) (hcoeff j) hf
  exact hcj.fun_mul (hs.fun_pow j)

theorem eventually_root_near {V : Type*} [TopologicalSpace V] {P : V → ℂ[X]} {x : V}
    (k : ℕ) (hp : ∀ y, (P y).Monic ∧ (P y).natDegree = k)
    (hcoeff : ∀ j, ContinuousAt (fun y => (P y).coeff j) x)
    {z : ℂ} (hz : (P x).eval z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∃ w, (P y).eval w = 0 ∧ dist z w < ε := by
  have hc := (continuousAt_eval k (fun y => (hp y).2.le) hcoeff z).norm
  have hsmall : ∀ᶠ y in 𝓝 x, ‖(P y).eval z‖ < ε ^ k :=
    hc.eventually_lt_const (by change ‖(P x).eval z‖ < ε ^ k; rw [hz, norm_zero]; exact pow_pos hε _)
  filter_upwards [hsmall] with y hy
  apply exists_root_near_of_eval_small (hp y).1 hε
  simpa only [(hp y).2] using hy

end Geometry.ComplexTorus.RiemannProjectivity.RootContinuityAt.Constructions.RootContinuity

namespace Geometry.ComplexTorus.RiemannProjectivity.RootContinuityAt.Constructions.RootClosure

/-! # RiemannProjectivity: extending containment of polynomial roots by closedness -/

open Set Filter _root_.Polynomial _root_.Metric
open scoped _root_.Topology

variable {V : Type*} [PseudoMetricSpace V]

theorem root_mem_closed {P : V → ℂ[X]} {S : Set (V × ℂ)} (hS : IsClosed S)
    (k : ℕ) (hp : ∀ y, (P y).Monic ∧ (P y).natDegree = k)
    {D : Set V} {x : V} (hx : x ∈ closure D)
    (hcoeff : ∀ j, ContinuousAt (fun y => (P y).coeff j) x)
    (hrootS : ∀ y ∈ D, ∀ z, (P y).eval z = 0 → (y, z) ∈ S)
    {z : ℂ} (hz : (P x).eval z = 0) : (x, z) ∈ S := by
  rw [← hS.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hnear := RootContinuity.eventually_root_near k hp hcoeff hz hε
  have hball : ∀ᶠ y in 𝓝 x, y ∈ ball x ε := isOpen_ball.mem_nhds (mem_ball_self hε)
  obtain ⟨y, hyD, hynear, hyball⟩ :=
    ((mem_closure_iff_frequently.mp hx).and_eventually (hnear.and hball)).exists
  obtain ⟨w, hw, hzw⟩ := hynear
  refine ⟨(y, w), hrootS y hyD w hw, ?_⟩
  rw [Prod.dist_eq]
  exact max_lt (by simpa only [mem_ball, dist_comm] using hyball) hzw

theorem root_imp_of_generic {P Q : V → ℂ[X]} (k d : ℕ)
    (hP : ∀ y, (P y).Monic ∧ (P y).natDegree = k)
    (hQdeg : ∀ y, (Q y).natDegree ≤ d)
    {D : Set V} {x : V} (hx : x ∈ closure D)
    (hPc : ∀ j, ContinuousAt (fun y => (P y).coeff j) x)
    (hQc : ∀ j, ContinuousAt (fun y => (Q y).coeff j) x)
    (himp : ∀ y ∈ D, ∀ z, (P y).eval z = 0 → (Q y).eval z = 0)
    {z : ℂ} (hz : (P x).eval z = 0) : (Q x).eval z = 0 := by
  have hclosure : (x, z) ∈ closure {p : V × ℂ | p.1 ∈ D ∧ (Q p.1).eval p.2 = 0} :=
    root_mem_closed (S := closure {p : V × ℂ | p.1 ∈ D ∧ (Q p.1).eval p.2 = 0})
      isClosed_closure k hP hx hPc
      (fun y hy w hw => subset_closure ⟨hy, himp y hy w hw⟩) hz
  exact tendsto_nhds_unique_of_frequently_eq
    (RootContinuity.continuousAt_eval_pair d hQdeg hQc z) continuousAt_const
    ((mem_closure_iff_frequently.mp hclosure).mono (fun _ hp => hp.2))

end Geometry.ComplexTorus.RiemannProjectivity.RootContinuityAt.Constructions.RootClosure

end

end OAI
