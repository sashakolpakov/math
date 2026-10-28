import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.BigOperators.Fin
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootMomentsNe

/-! # Disk Factorization On -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.DiskFactorizationOn.Constructions.DiskFactorization

noncomputable section

/-!
# Polynomial extraction of zeros on a disk

An analytic function on a neighborhood of a closed disk, nonzero somewhere
in the disk, factors there as a monic polynomial times an analytic unit.
The polynomial is constructed from the actual finite divisor of zeros.
-/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology BigOperators

def divisorPolynomial (D : ℂ → ℤ) (hD : D.HasFiniteSupport) : Polynomial ℂ :=
  ∏ a ∈ hD.toFinset, (X - C a) ^ (D a).toNat

theorem divisorPolynomial_monic (D : ℂ → ℤ) (hD : D.HasFiniteSupport) :
    (divisorPolynomial D hD).Monic :=
  monic_prod_of_monic _ _ (fun a _ => (monic_X_sub_C a).pow _)

theorem eval_divisorPolynomial (D : ℂ → ℤ) (hD : D.HasFiniteSupport)
    (hDn : ∀ a, 0 ≤ D a) (z : ℂ) :
    (divisorPolynomial D hD).eval z = (∏ᶠ a, (· - a) ^ D a) z := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hD.toFinset)]
  · simp only [divisorPolynomial, eval_prod, eval_pow, eval_sub, eval_X, eval_C,
      Finset.prod_apply, Pi.pow_apply]
    apply Finset.prod_congr rfl
    intro a _
    conv_rhs => rw [← Int.toNat_of_nonneg (hDn a), zpow_natCast]
  · rw [Function.FactorizedRational.mulSupport]
    intro a ha
    exact hD.mem_toFinset.mpr ha

theorem root_mem_divisor_support (D : ℂ → ℤ) (hD : D.HasFiniteSupport) {z : ℂ}
    (hz : (divisorPolynomial D hD).eval z = 0) : z ∈ Function.support D := by
  simp only [divisorPolynomial, eval_prod, eval_pow, eval_sub, eval_X, eval_C] at hz
  obtain ⟨a, ha, hza⟩ := Finset.prod_eq_zero_iff.mp hz
  have h : z = a := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hza)
  rw [h]
  exact hD.mem_toFinset.mp ha

/-- Continuous functions agreeing off a discrete exceptional set agree on
the whole open domain. -/
theorem eqOn_of_eq_codiscrete {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : ∀ x ∈ U, ContinuousAt f x) (hg : ∀ x ∈ U, ContinuousAt g x)
    (heq : f =ᶠ[codiscreteWithin U] g) : EqOn f g U := by
  intro x hx
  have hne : f =ᶠ[𝓝[≠] x] g := by
    have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp heq) x hx
    filter_upwards [h, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)] with z hz hzU
    rcases hz with hz | hz
    · exact hz
    · exact False.elim (hz hzU)
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hf x hx).mono_left nhdsWithin_le_nhds)
    ((hg x hx).mono_left nhdsWithin_le_nhds) hne

/-- The zero divisor is finite by compactness and has nonnegative integer
multiplicities by analyticity. Its polynomial extracts exactly these zeros. -/
theorem exists_polynomial_unit_on_disk {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hn : ∃ z ∈ ball c R, f z ≠ 0) :
    ∃ P : Polynomial ℂ, P.Monic ∧ (∀ z, P.eval z = 0 → z ∈ ball c R) ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball c R) ∧ (∀ z ∈ ball c R, g z ≠ 0) ∧
      ∀ z ∈ ball c R, f z = P.eval z * g z := by
  have hfa := hf.mono ball_subset_closedBall
  obtain ⟨z₀, hz₀, hfz₀⟩ := hn
  have horder₀ : meromorphicOrderAt f z₀ ≠ ⊤ := by
    rw [(hfa z₀ hz₀).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz₀]
    exact WithTop.coe_ne_top
  have horder : ∀ z ∈ ball c R, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz
    exact hfa.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_ball c R).isPreconnected hz₀ hz horder₀
  let D : ℂ → ℤ := MeromorphicOn.divisor f (ball c R)
  have hD : D.HasFiniteSupport := hf.meromorphicOn.divisor_ball_support_finite
  have hDn : ∀ a, 0 ≤ D a := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa
  let P := divisorPolynomial D hD
  obtain ⟨g, hg, hgn, heq⟩ := hfa.meromorphicOn.extract_zeros_poles
    (fun z => horder z z.property) hD
  refine ⟨P, divisorPolynomial_monic D hD, ?_, g, hg, fun z hz => hgn ⟨z, hz⟩, ?_⟩
  · intro z hz
    exact (MeromorphicOn.divisor f (ball c R)).supportWithinDomain
      (root_mem_divisor_support D hD hz)
  · apply eqOn_of_eq_codiscrete isOpen_ball
      (fun z hz => (hfa z hz).continuousAt)
      (fun z hz => P.continuous.continuousAt.mul (hg z hz).continuousAt)
    filter_upwards [heq] with z hz
    simpa only [Pi.smul_apply, smul_eq_mul, P, eval_divisorPolynomial D hD hDn] using hz

/-- Enumerate all roots of a monic complex polynomial, with multiplicities. -/
theorem exists_root_tuple (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ (d : ℕ) (roots : Fin d → ℂ),
      (∀ i, P.eval (roots i) = 0) ∧ ∀ z, P.eval z = RootMomentsNe.Constructions.RootMoments.rootProduct roots z := by
  let l := P.roots.toList
  let roots : Fin l.length → ℂ := l.get
  refine ⟨l.length, roots, ?_, ?_⟩
  · intro i
    apply (mem_roots hP.ne_zero).mp
    exact Multiset.mem_toList.mp (List.getElem_mem i.isLt)
  · intro z
    rw [(IsAlgClosed.splits P).eval_eq_prod_roots_of_monic hP]
    symm
    change Finset.univ.prod (fun i : Fin l.length => z - l.get i) = _
    rw [← Fin.prod_ofFn]
    change (List.ofFn ((fun a : ℂ => z - a) ∘ l.get)).prod = _
    rw [← List.map_ofFn, List.ofFn_get]
    change (↑(l.map (fun a => z - a)) : Multiset ℂ).prod = _
    rw [← Multiset.map_coe]
    simp only [l, Multiset.coe_toList]

/-- Actual disk zeros admit a finite tuple factorization suitable for the
contour-moment formulas. No root data are supplied as hypotheses. -/
theorem exists_root_tuple_unit_on_disk {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hn : ∃ z ∈ ball c R, f z ≠ 0) :
    ∃ (d : ℕ) (roots : Fin d → ℂ) (g : ℂ → ℂ),
      (∀ i, roots i ∈ ball c R) ∧ AnalyticOnNhd ℂ g (ball c R) ∧
      (∀ z ∈ ball c R, g z ≠ 0) ∧
      ∀ z ∈ ball c R, f z = RootMomentsNe.Constructions.RootMoments.rootProduct roots z * g z := by
  obtain ⟨P, hP, hPr, g, hg, hgn, hfg⟩ := exists_polynomial_unit_on_disk hf hn
  obtain ⟨d, roots, hroots, hPeval⟩ := exists_root_tuple P hP
  refine ⟨d, roots, g, fun i => hPr _ (hroots i), hg, hgn, ?_⟩
  intro z hz
  rw [hfg z hz, hPeval]

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.DiskFactorizationOn.Constructions.DiskFactorization
