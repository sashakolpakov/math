import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Algebra.Polynomial

/-! # Resultant Norm -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNorm.Rigidity

noncomputable section

/-! Norms of all polynomial resultants determine a monic polynomial over
a nontrivially normed field, with no splitting hypothesis. The cancellation
step uses scalar perturbations of each test polynomial. -/

open _root_.Polynomial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [NontriviallyNormedField K]

theorem resultant_right_degree (P R : Polynomial K) (hP : P.Monic)
    (n : ℕ) (hn : R.natDegree ≤ n) :
    P.resultant R P.natDegree n = P.resultant R := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree, hP.leadingCoeff, one_pow, one_mul]

def perturbation (P R : Polynomial K) : Polynomial K :=
  (P.map C).resultant (R.map C + C X) P.natDegree R.natDegree

theorem perturbation_eval (P R : Polynomial K) (x : K) :
    (perturbation P R).eval x = P.resultant (R + C x) P.natDegree R.natDegree := by
  have hm (S : Polynomial K) : (S.map C).map (evalRingHom x) = S := by
    ext i
    simp
  change (evalRingHom x) ((P.map C).resultant (R.map C + C X) P.natDegree R.natDegree) = _
  rw [← resultant_map_map, hm, Polynomial.map_add, hm, Polynomial.map_C]
  change P.resultant (R + C (Polynomial.eval x X)) P.natDegree R.natDegree = _
  rw [eval_X]

theorem continuous_perturbation (P R : Polynomial K) :
    Continuous (fun x : K => P.resultant (R + C x) P.natDegree R.natDegree) := by
  simpa only [perturbation_eval] using (perturbation P R).continuous

theorem finite_bad_constants (P R : Polynomial K) (hP : P.Monic) :
    Set.Finite {x : K | P.resultant (R + C x) P.natDegree R.natDegree = 0} := by
  classical
  let L := AlgebraicClosure K
  let ι : K →+* L := algebraMap K L
  let S : Set L := (fun a => -(R.map ι).eval a) '' ((P.map ι).roots.toFinset : Set L)
  have hS : S.Finite := (Finset.finite_toSet _).image _
  apply (hS.preimage ι.injective.injOn).subset
  intro x hx
  have hx' := congrArg ι hx
  rw [map_zero, ← resultant_map_map] at hx'
  have hdeg : ((R + C x).map ι).natDegree ≤ R.natDegree :=
    natDegree_map_le.trans ((natDegree_add_le _ _).trans (by simp))
  have he := resultant_eq_prod_eval (P.map ι) ((R + C x).map ι) R.natDegree hdeg
    (IsAlgClosed.splits _)
  rw [natDegree_map_eq_of_injective ι.injective, (hP.map ι).leadingCoeff, one_pow, one_mul] at he
  rw [he] at hx'
  obtain ⟨a, ha, hyzero⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hx')
  refine ⟨a, Multiset.mem_toFinset.mpr ha, ?_⟩
  simp only [Polynomial.map_add, Polynomial.map_C, eval_add, eval_C] at hyzero
  exact (eq_neg_of_add_eq_zero_right hyzero).symm

theorem dense_compl_finite (S : Set K) (hS : S.Finite) : Dense Sᶜ := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | @insert a S ha hS ih =>
    rw [show (insert a S)ᶜ = Sᶜ ∩ {a}ᶜ by ext x; simp [and_comm]]
    exact ih.inter_of_isOpen_right (dense_compl_singleton a) isOpen_compl_singleton

theorem resultant_mul_monic (H P R : Polynomial K) (hH : H.Monic) (hP : P.Monic) :
    (H * P).resultant R = H.resultant R * P.resultant R := by
  rw [natDegree_mul hH.ne_zero hP.ne_zero]
  exact resultant_mul_left H P R R.natDegree le_rfl

theorem cancel_monic_factor (H P Q : Polynomial K)
    (hH : H.Monic) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ R : Polynomial K, ‖(H * P).resultant R‖ = ‖(H * Q).resultant R‖) :
    ∀ R : Polynomial K, ‖P.resultant R‖ = ‖Q.resultant R‖ := by
  intro R
  have he : (fun x : K => ‖P.resultant (R + C x) P.natDegree R.natDegree‖) =
      fun x : K => ‖Q.resultant (R + C x) Q.natDegree R.natDegree‖ := by
    apply Continuous.ext_on (dense_compl_finite _ (finite_bad_constants H R hH))
      (continuous_perturbation P R).norm (continuous_perturbation Q R).norm
    intro x hx
    have hdeg : (R + C x).natDegree ≤ R.natDegree :=
      (natDegree_add_le _ _).trans (by simp)
    have hh := h (R + C x)
    rw [resultant_mul_monic H P _ hH hP, resultant_mul_monic H Q _ hH hQ,
      norm_mul, norm_mul] at hh
    rw [← resultant_right_degree H _ hH _ hdeg, ← resultant_right_degree P _ hP _ hdeg,
      ← resultant_right_degree Q _ hQ _ hdeg] at hh
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hx) hh
  have hz := congrFun he 0
  change ‖P.resultant (R + C (0 : K)) P.natDegree R.natDegree‖ =
    ‖Q.resultant (R + C (0 : K)) Q.natDegree R.natDegree‖ at hz
  rw [Polynomial.C_0, add_zero] at hz
  exact hz

theorem monic_eq_of_norm_resultant_eq (P Q : Polynomial K)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ R : Polynomial K, ‖P.resultant R‖ = ‖Q.resultant R‖) : P = Q := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P Q with
  | h n ih =>
    by_cases hz : P.natDegree = 0
    · rw [eq_one_of_monic_natDegree_zero hP hz, eq_one_of_monic_natDegree_zero hQ (hdeg.symm.trans hz)]
    have hunit : ¬ IsUnit P := by
      intro hu
      exact hz (natDegree_eq_zero_of_isUnit hu)
    obtain ⟨H, hH, hI, P', hPP⟩ := P.exists_monic_irreducible_factor hunit
    have hzP : P.resultant H = 0 := resultant_eq_zero_iff.mpr ⟨Or.inl hP.ne_zero, by
      intro hc
      exact (hI.dvd_iff_not_isCoprime.mp ⟨P', hPP⟩) hc.symm⟩
    have hzQ : Q.resultant H = 0 := by
      have hh := h H
      rw [hzP, norm_zero] at hh
      exact norm_eq_zero.mp hh.symm
    have hdQ : H ∣ Q := hI.dvd_iff_not_isCoprime.mpr (by
      intro hc
      exact (resultant_eq_zero_iff.mp hzQ).2 hc.symm)
    obtain ⟨Q', hQQ⟩ := hdQ
    have hP' : P'.Monic := hH.of_mul_monic_left (hPP ▸ hP)
    have hQ' : Q'.Monic := hH.of_mul_monic_left (hQQ ▸ hQ)
    have heP : P.natDegree = H.natDegree + P'.natDegree := by
      rw [hPP, natDegree_mul hH.ne_zero hP'.ne_zero]
    have heQ : Q.natDegree = H.natDegree + Q'.natDegree := by
      rw [hQQ, natDegree_mul hH.ne_zero hQ'.ne_zero]
    have hHpos : 0 < H.natDegree := hI.natDegree_pos
    have hc : ∀ R : Polynomial K, ‖(H * P').resultant R‖ = ‖(H * Q').resultant R‖ := by
      intro R
      rw [← hPP, ← hQQ]
      exact h R
    have he := ih P'.natDegree (by omega) P' Q' hP' hQ' (by omega)
      (cancel_monic_factor H P' Q' hH hP' hQ' hc) rfl
    rw [hPP, hQQ, he]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNorm.Rigidity
