import OAI.AlgebraicGeometry.Comparison.Betti.JointWeierstrassPreparation
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Distinguished Preparation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.DistinguishedPreparation.Weierstrass

noncomputable section

/-! A nonzero vertical germ admits preparation whose central polynomial
is a power of the centered coordinate. -/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology

theorem monic_eq_centered_power (P : ℂ[X]) (hP : P.Monic) (c : ℂ)
    (hroot : ∀ z : ℂ, P.eval z = 0 → z = c) :
    P = (X - C c) ^ P.natDegree := by
  have hs := IsAlgClosed.splits P
  have he : P.roots.map (fun z => X - C z) = P.roots.map (fun _ => (X - C c : ℂ[X])) := by
    apply Multiset.map_congr rfl
    intro z hz
    rw [hroot z ((mem_roots hP.ne_zero).mp hz)]
  calc
    P = (P.roots.map (fun z => X - C z)).prod := hs.eq_prod_roots_of_monic hP
    _ = (X - C c) ^ P.natDegree := by
      rw [he, Multiset.map_const', Multiset.prod_replicate, ← hs.natDegree_eq_card_roots]

theorem exists_distinguished_preparation
    {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ} {W : Set ((Fin n → ℂ) × ℂ)}
    (hW : IsOpen W) (hF : DifferentiableOn ℂ F W)
    {x : Fin n → ℂ} {c : ℂ} (hxc : (x, c) ∈ W)
    (hn : ¬∀ᶠ z in 𝓝 c, F (x, z) = 0) :
    ∃ (R : ℝ) (d : ℕ) (U : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → Polynomial ℂ)
        (q : (Fin n → ℂ) × ℂ → ℂ),
      0 < R ∧ IsOpen U ∧ x ∈ U ∧
      (∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U) ∧
      (∀ y ∈ U, (P y).Monic ∧ (P y).natDegree = d) ∧
      P x = (X - C c) ^ d ∧ DifferentiableOn ℂ q (U ×ˢ ball c R) ∧
      (∀ p ∈ U ×ˢ ball c R, q p ≠ 0) ∧
      ∀ p ∈ U ×ˢ ball c R, F p = (P p.1).eval p.2 * q p := by
  have ha : AnalyticAt ℂ (fun z => F (x, z)) c :=
    ComplexGroups.HolomorphicAlgebraicity.RootFamiliesAt.Constructions.RootFamilies.analyticOnNhd_slice hW hF x (K := {c})
      (by simpa using hxc) c (mem_singleton c)
  have hp := eventually_nhdsWithin_iff.mp
    (ha.eventually_eq_zero_or_eventually_ne_zero.resolve_left hn)
  have hdomain : ∀ᶠ z in 𝓝 c, (x, z) ∈ W :=
    (hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hxc
  obtain ⟨R, hR, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hdomain.and hp)
  have hbase : ∀ z ∈ closedBall c R, (x, z) ∈ W := fun z hz => (hball hz).1
  have hboundary : ∀ z ∈ sphere c R, F (x, z) ≠ 0 := by
    intro z hz
    exact (hball (sphere_subset_closedBall hz)).2 (ne_of_mem_sphere hz hR.ne')
  obtain ⟨d, U, P, q, hU, hx, _, hcoeff, hP, hq, hqn, hfactor⟩ :=
    JointWeierstrassPreparation.exists_joint_polynomial_preparation hW hF hR hbase hboundary
  have hroot : ∀ z : ℂ, (P x).eval z = 0 → z = c := by
    intro z hz
    by_contra hzc
    have hzb := (hP x hx).2.2 z hz
    have hnz := (hball (ball_subset_closedBall hzb)).2 hzc
    apply hnz
    rw [hfactor (x, z) ⟨hx, hzb⟩, hz, zero_mul]
  have hcenter := monic_eq_centered_power (P x) (hP x hx).1 c hroot
  rw [(hP x hx).2.1] at hcenter
  exact ⟨R, d, U, P, q, hR, hU, hx, hcoeff,
    fun y hy => ⟨(hP y hy).1, (hP y hy).2.1⟩, hcenter, hq, hqn, hfactor⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.DistinguishedPreparation.Weierstrass
