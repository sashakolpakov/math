import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType

/-! # Galois Valuation Cm -/

namespace OAI.RepresentationTheory.Hecke.GaloisValuationCm

noncomputable section

/-!
# GaloisValuation: Galois signs of parameter valuations

The target already supplies the specialized outputs needed from the graph:
LefschetzNormalization supplies the normalized sign and conjugate-pair representatives; RadialDilation
supplies the finite phase, dilation identity, and unit absolute values;
SphericalAction supplies the dilation root and its possible inverse; RationalStructure supplies
scalar equivariance of projective Satake parameters. These are explicit
named hypotheses below. The full geometric propositions are unnecessary
for this arithmetic implication. No statement stub is imported.

The concrete valuation, restriction map, and Satake realization remain
the interfaces in the committed specification. Its reserved binder `Σ`
is spelled `reps` here. No additional substantive hypothesis is imposed.
The active-representative, norm-one, ultrametric, and normalization hypotheses
are retained, although the explicit split-order formula and unit-absolute-value
input make them unnecessary for this implication.
-/

open scoped Classical
open OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

abbrev Qbar := AlgebraicClosure ℚ

def parameterTriple (s e : Qbar) : Fin 3 → Qbar := ![s, s⁻¹, e]

def ProjectivelyEqual (a b : Fin 3 → Qbar) : Prop :=
  ∃ z : Qbar, z ≠ 0 ∧
    ∃ p : Equiv.Perm (Fin 3), ∀ i, a i = z * b (p i)

section Valuation

variable {K : Type*} [Field K] (ν : K → ℚ)
  (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → ν (x * y) = ν x + ν y)

include hmul

lemma val_one : ν 1 = 0 := by
  have h := hmul 1 1 one_ne_zero one_ne_zero
  simp only [one_mul] at h
  linarith

lemma val_pow (x : K) (hx : x ≠ 0) (n : ℕ) :
    ν (x ^ n) = (n : ℚ) * ν x := by
  induction n with
  | zero => simp [val_one ν hmul]
  | succ n ih =>
    rw [pow_succ, hmul _ _ (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

lemma val_inv (x : K) (hx : x ≠ 0) : ν x⁻¹ = -ν x := by
  have h := hmul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, val_one ν hmul] at h
  linarith

lemma val_zpow (x : K) (hx : x ≠ 0) (n : ℤ) :
    ν (x ^ n) = (n : ℚ) * ν x := by
  cases n with
  | ofNat n => simpa using val_pow ν hmul x hx n
  | negSucc n =>
    rw [zpow_negSucc, val_inv ν hmul _ (pow_ne_zero _ hx), val_pow ν hmul x hx]
    push_cast
    ring

lemma val_neg (x : K) (hx : x ≠ 0) : ν (-x) = ν x := by
  have h := val_pow ν hmul (-1) (neg_ne_zero.mpr one_ne_zero) 2
  simp only [even_two, Even.neg_pow, one_pow, val_one ν hmul, Nat.cast_ofNat] at h
  have hn : ν (-1) = 0 := by linarith
  rw [← neg_one_mul x, hmul _ _ (neg_ne_zero.mpr one_ne_zero) hx, hn, zero_add]

lemma val_torsion (z : K) (hz : ∃ n : ℕ, 0 < n ∧ z ^ n = 1) :
    z ≠ 0 ∧ ν z = 0 := by
  obtain ⟨n, hn, hzn⟩ := hz
  have hz0 : z ≠ 0 := by
    intro h
    simp [h, Nat.ne_of_gt hn] at hzn
  have h := val_pow ν hmul z hz0 n
  rw [hzn, val_one ν hmul] at h
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact ⟨hz0, (mul_eq_zero.mp h.symm).resolve_left hn0⟩

lemma val_prod {I : Type*} (a : Finset I) (f : I → K)
    (hf : ∀ i ∈ a, f i ≠ 0) :
    ν (∏ i ∈ a, f i) = ∑ i ∈ a, ν (f i) := by
  induction a using Finset.induction_on with
  | empty => simp [val_one ν hmul]
  | @insert i a hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [hmul _ _ (hf i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj)))]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

end Valuation

lemma split_sum {G : Type*} [Group G]
    (c : G) (hc : c ≠ 1) (hcentral : ∀ g : G, Commute c g)
    (d : G → ℤ) (hodd : ∀ g, d (c * g) = -d g)
    (reps : Finset G) (hp : ∀ g, g ∈ reps ↔ c * g ∉ reps)
    (g : G) (ε : ℤ) (M : ℚ) :
    (∑ τ ∈ reps, (ε * 3 * d τ : ℤ) *
      (if g * τ = c then M else if g * τ = 1 then -M else 0)) =
      -(ε : ℚ) * 3 * (d g⁻¹ : ℚ) * M := by
  have h1 (τ : G) : g * τ = 1 ↔ τ = g⁻¹ := by
    constructor
    · intro h
      have := congrArg (fun x => g⁻¹ * x) h
      simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using this
    · rintro rfl
      exact mul_inv_cancel g
  have hc' (τ : G) : g * τ = c ↔ τ = c * g⁻¹ := by
    constructor
    · intro h
      have := congrArg (fun x => g⁻¹ * x) h
      simpa only [← mul_assoc, inv_mul_cancel, one_mul, ← (hcentral g⁻¹).eq] using this
    · rintro rfl
      rw [← mul_assoc, ← (hcentral g).eq, mul_assoc, mul_inv_cancel, mul_one]
  by_cases ha : g⁻¹ ∈ reps
  · have hb := (hp g⁻¹).mp ha
    rw [Finset.sum_eq_single g⁻¹]
    · simp only [mul_inv_cancel, ite_eq_left, ite_eq_right (Ne.symm hc)]
      push_cast
      ring
    · intro τ hτ hne
      have hnc : g * τ ≠ c := fun h => hb ((hc' τ).mp h ▸ hτ)
      have hn1 : g * τ ≠ 1 := fun h => hne ((h1 τ).mp h)
      simp only [ite_eq_right hnc, ite_eq_right hn1, mul_zero]
    · exact fun h => (h ha).elim
  · have hb : c * g⁻¹ ∈ reps := by
      by_contra h
      exact ha ((hp g⁻¹).mpr h)
    rw [Finset.sum_eq_single (c * g⁻¹)]
    · rw [ite_eq_left ((hc' _).mpr rfl), hodd]
      push_cast
      ring
    · intro τ hτ hne
      have hnc : g * τ ≠ c := fun h => hne ((hc' τ).mp h)
      have hn1 : g * τ ≠ 1 := fun h => ha ((h1 τ).mp h ▸ hτ)
      simp only [ite_eq_right hnc, ite_eq_right hn1, mul_zero]
    · exact fun h => (h hb).elim

section CM

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

omit [IsGalois ℚ E] in
lemma cm_conj_inv : (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)⁻¹ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by
  apply inv_eq_of_mul_eq_one_left
  apply AlgEquiv.ext
  intro x
  exact AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E x

omit [IsGalois ℚ E] in
lemma inverse_sign_odd
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (d : Gal(E/ℚ) → ℤ) (hd : ∀ τ, d τ = AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
    (τ : Gal(E/ℚ)) : d (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = -d τ := by
  rw [hd, hd, mul_inv_rev, cm_conj_inv, ← (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E τ⁻¹).eq,
    v.property, AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue_not]

end CM

lemma projective_refl (a : Fin 3 → Qbar) : ProjectivelyEqual a a := by
  exact ⟨1, one_ne_zero, Equiv.refl _, fun _ => (one_mul _).symm⟩

lemma projective_symm {a b : Fin 3 → Qbar} (h : ProjectivelyEqual a b) :
    ProjectivelyEqual b a := by
  obtain ⟨z, hz, p, hp⟩ := h
  refine ⟨z⁻¹, inv_ne_zero hz, p.symm, ?_⟩
  intro i
  rw [hp, p.apply_symm_apply, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

lemma projective_trans {a b c : Fin 3 → Qbar}
    (hab : ProjectivelyEqual a b) (hbc : ProjectivelyEqual b c) :
    ProjectivelyEqual a c := by
  obtain ⟨z, hz, p, hp⟩ := hab
  obtain ⟨w, hw, r, hr⟩ := hbc
  refine ⟨z * w, mul_ne_zero hz hw, p.trans r, ?_⟩
  intro i
  rw [hp, hr]
  exact (mul_assoc _ _ _).symm

lemma triple_ratio (q : ℕ) (hq : q.Prime)
    (s e : Qbar) (hs : s ^ 2 = (q : Qbar))
    (j : Qbar →ₐ[ℚ] ℂ) (he : ‖j e‖ = 1)
    (a b : Fin 3)
    (hab : parameterTriple s e a = (q : Qbar) * parameterTriple s e b) :
    a = 0 ∧ b = 1 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hsq : ‖j s‖ ^ 2 = (q : ℝ) := by
    have h := congrArg (fun x : Qbar => ‖j x‖) hs
    simpa only [map_pow, norm_pow, map_natCast, Complex.norm_natCast] using h
  have hspos : 0 < ‖j s‖ := by
    have := norm_nonneg (j s)
    nlinarith
  have hs1 : 1 < ‖j s‖ := by nlinarith
  have habn := congrArg (fun x : Qbar => ‖j x‖) hab
  simp only [map_mul, norm_mul, map_natCast, Complex.norm_natCast] at habn
  fin_cases a <;> fin_cases b
  all_goals try exact ⟨rfl, rfl⟩
  all_goals norm_num [parameterTriple, he] at habn
  all_goals try field_simp at habn
  all_goals nlinarith [sq_nonneg (‖j s‖ - 1)]

lemma projective_parameter_unique
    (q : ℕ) (hq : q.Prime) (s t e x : Qbar)
    (hs : s ^ 2 = (q : Qbar)) (ht : t ^ 2 = (q : Qbar))
    (j : Qbar →ₐ[ℚ] ℂ) (he : ‖j e‖ = 1)
    (h : ProjectivelyEqual (parameterTriple s x) (parameterTriple t e)) :
    x = e ∨ x = -e := by
  have hq0 : (q : Qbar) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; exact hq0 hs.symm
  have ht0 : t ≠ 0 := by intro h; simp [h] at ht; exact hq0 ht.symm
  obtain ⟨z, hz, p, hp⟩ := h
  have hratio : parameterTriple t e (p 0) = (q : Qbar) * parameterTriple t e (p 1) := by
    apply mul_left_cancel₀ hz
    calc
      z * parameterTriple t e (p 0) = s := (hp 0).symm
      _ = (q : Qbar) * s⁻¹ := by rw [← hs, pow_two]; field_simp
      _ = (q : Qbar) * (z * parameterTriple t e (p 1)) := by rw [← hp 1]; rfl
      _ = z * ((q : Qbar) * parameterTriple t e (p 1)) := by ring
  obtain ⟨hp0, hp1⟩ := triple_ratio q hq t e ht j he (p 0) (p 1) hratio
  have hp2 : p 2 = 2 := by
    have h20 : p 2 ≠ p 0 := p.injective.ne (by decide)
    have h21 : p 2 ≠ p 1 := p.injective.ne (by decide)
    rw [hp0] at h20
    rw [hp1] at h21
    omega
  have hst : s = z * t := by simpa [parameterTriple, hp0] using hp 0
  have hxe : x = z * e := by simpa [parameterTriple, hp2] using hp 2
  have hzsq : z ^ 2 = 1 := by
    apply mul_right_cancel₀ hq0
    calc
      z ^ 2 * (q : Qbar) = (z * t) ^ 2 := by rw [mul_pow, ht]
      _ = (q : Qbar) := by rw [← hst, hs]
      _ = 1 * (q : Qbar) := (one_mul _).symm
  rcases sq_eq_one_iff.mp hzsq with hz1 | hz1
  · left
    simpa [hz1] using hxe
  · right
    simpa [hz1] using hxe

lemma dilation_root_valuation
    {E : Type*} [Field E] [Algebra ℚ E]
    (ιE : E →ₐ[ℚ] Qbar)
    (res : Gal(Qbar/ℚ) →* Gal(E/ℚ))
    (hres : ∀ (σ : Gal(Qbar/ℚ)) (x : E), σ (ιE x) = ιE ((res σ) x))
    (c : Gal(E/ℚ)) (hc : c ≠ 1) (hcentral : ∀ g, Commute c g)
    (d : Gal(E/ℚ) → ℤ) (hodd : ∀ g, d (c * g) = -d g)
    (reps : Finset (Gal(E/ℚ)))
    (hp : ∀ g : Gal(E/ℚ), g ∈ reps ↔ c * g ∉ reps)
    (r : Eˣ) (M : ℕ) (hM : 0 < M)
    (ν : Qbar → ℚ)
    (hmul : ∀ x y : Qbar, x ≠ 0 → y ≠ 0 → ν (x * y) = ν x + ν y)
    (hsplit : ∀ τ : Gal(E/ℚ), ν (ιE (τ (r : E))) =
      if τ = c then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (e₀ ω ζ : Qbar) (he₀ : e₀ ≠ 0) (ε : ℤ)
    (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hrelation : ω ^ 2 =
      ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (ε * 3 * d τ))
    (hroot : e₀ ^ M = ω) (σ : Gal(Qbar/ℚ)) :
    ν (σ e₀) = -(ε : ℚ) * 3 / 2 * (d ((res σ)⁻¹) : ℚ) := by
  have hω : ω ≠ 0 := hroot ▸ pow_ne_zero M he₀
  have hσω : σ ω ≠ 0 := (map_ne_zero σ).mpr hω
  have hσe : σ e₀ ≠ 0 := (map_ne_zero σ).mpr he₀
  have hσζ : ∃ n : ℕ, 0 < n ∧ (σ ζ) ^ n = 1 := by
    obtain ⟨n, hn, hzn⟩ := hζ
    exact ⟨n, hn, by rw [← map_pow, hzn, map_one]⟩
  obtain ⟨hσζ0, hσζval⟩ := val_torsion ν hmul (σ ζ) hσζ
  have ht0 (τ : Gal(E/ℚ)) : σ (ιE (τ (r : E))) ≠ 0 := by
    exact (map_ne_zero σ).mpr ((map_ne_zero ιE).mpr
      ((map_ne_zero τ).mpr (Units.ne_zero r)))
  have hσrelation : (σ ω) ^ 2 =
      σ ζ * ∏ τ ∈ reps, (σ (ιE (τ (r : E)))) ^ (ε * 3 * d τ) := by
    simpa only [map_pow, map_mul, map_prod, map_zpow₀] using congrArg σ hrelation
  have hvω : (2 : ℚ) * ν (σ ω) =
      -(ε : ℚ) * 3 * (d ((res σ)⁻¹) : ℚ) * (M : ℚ) := by
    calc
      (2 : ℚ) * ν (σ ω) = ν ((σ ω) ^ 2) := (val_pow ν hmul _ hσω 2).symm
      _ = ν (σ ζ * ∏ τ ∈ reps,
          (σ (ιE (τ (r : E)))) ^ (ε * 3 * d τ)) := congrArg ν hσrelation
      _ = ν (σ ζ) + ν (∏ τ ∈ reps,
          (σ (ιE (τ (r : E)))) ^ (ε * 3 * d τ)) :=
        hmul _ _ hσζ0 (Finset.prod_ne_zero_iff.mpr (fun τ _ => zpow_ne_zero _ (ht0 τ)))
      _ = ∑ τ ∈ reps, ν ((σ (ιE (τ (r : E)))) ^ (ε * 3 * d τ)) := by
        rw [hσζval, zero_add, val_prod ν hmul reps _
          (fun τ _ => zpow_ne_zero _ (ht0 τ))]
      _ = ∑ τ ∈ reps, (ε * 3 * d τ : ℤ) *
          (if res σ * τ = c then (M : ℚ)
           else if res σ * τ = 1 then -(M : ℚ) else 0) := by
        apply Finset.sum_congr rfl
        intro τ _
        rw [val_zpow ν hmul _ (ht0 τ), hres]
        change (ε * 3 * d τ : ℤ) * ν (ιE ((res σ * τ) (r : E))) = _
        rw [hsplit]
      _ = -(ε : ℚ) * 3 * (d ((res σ)⁻¹) : ℚ) * (M : ℚ) :=
        split_sum c hc hcentral d hodd reps hp (res σ) ε (M : ℚ)
  have hvroot : (M : ℚ) * ν (σ e₀) = ν (σ ω) := by
    rw [← val_pow ν hmul _ hσe, ← map_pow, hroot]
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  apply mul_right_cancel₀ hM0
  nlinarith [hvω, hvroot]

lemma conjugate_triple (σ : Gal(Qbar/ℚ)) (s e : Qbar) :
    (fun i => σ (parameterTriple s e i)) = parameterTriple (σ s) (σ e) := by
  funext i
  fin_cases i <;> simp [parameterTriple]

lemma normalize_conjugate_triple (q : ℕ) (s e : Qbar)
    (hs : s ^ 2 = (q : Qbar)) (σ : Gal(Qbar/ℚ)) :
    ∃ eσ : Qbar, ProjectivelyEqual
      (fun i => σ (parameterTriple s e i)) (parameterTriple s eσ) := by
  have hsσ : (σ s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, map_natCast]
  rw [conjugate_triple]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsσ with h | h
  · refine ⟨σ e, ?_⟩
    rw [h]
    exact projective_refl _
  · refine ⟨-(σ e), -1, neg_ne_zero.mpr one_ne_zero, Equiv.refl _, ?_⟩
    intro i
    fin_cases i <;> simp [parameterTriple, h]

/-- The target implication, with the prerequisite outputs explicitly named. -/
theorem galois_sign_rule_for_parameter_valuations
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (ιE : E →ₐ[ℚ] Qbar)
    (res : Gal(Qbar/ℚ) →* Gal(E/ℚ))
    (hres : ∀ (σ : Gal(Qbar/ℚ)) (x : E),
      σ (ιE x) = ιE ((res σ) x))
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hLefschetzNormalization_normalized : v.val 1 = true)
    (d : Gal(E/ℚ) → ℤ)
    (hLefschetzNormalization_sign : ∀ τ, d τ = AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
    (reps : Finset (Gal(E/ℚ)))
    (_hL2_8_active : (1 : Gal(E/ℚ)) ∈ reps)
    (hLefschetzNormalization_representatives : ∀ τ : Gal(E/ℚ),
      τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (q : ℕ) (hq : q.Prime)
    (M : ℕ) (hM : 0 < M)
    (r : Eˣ)
    (_hnorm : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (ν : Qbar → ℚ)
    (hν_mul : ∀ x y : Qbar, x ≠ 0 → y ≠ 0 →
      ν (x * y) = ν x + ν y)
    (_hν_add : ∀ x y : Qbar,
      x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (ν x) (ν y) ≤ ν (x + y))
    (_hν_q : ν (q : Qbar) = 1)
    (hsplit : ∀ τ : Gal(E/ℚ),
      ν (ιE (τ (r : E))) =
        if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ)
        else if τ = 1 then -(M : ℚ)
        else 0)
    (e₀ e ω ζ : Qbar)
    (ε : ℤ) (hRadialDilation_convention : ε = 1 ∨ ε = -1)
    (hRadialDilation_phase : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
    (hRadialDilation_relation : ω ^ 2 =
      ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (ε * 3 * d τ))
    (hSphericalAction_root : e₀ ^ M = ω)
    (hSphericalAction_parameter : e = e₀ ∨ e = e₀⁻¹)
    (j : Qbar →ₐ[ℚ] ℂ)
    (hRadialDilation_unit : ∀ σ : Gal(Qbar/ℚ), ‖j (σ e)‖ = 1)
    (s : Qbar) (hs : s ^ 2 = (q : Qbar))
    (P : Gal(Qbar/ℚ) → Fin 3 → Qbar)
    (hRationalStructure : ∀ σ : Gal(Qbar/ℚ),
      ProjectivelyEqual (P σ)
        (fun i => σ (parameterTriple s e i))) :
    (ν e = (-3 / 2 : ℚ) ∨ ν e = (3 / 2 : ℚ)) ∧
    ∀ σ : Gal(Qbar/ℚ),
      ν (σ e) = (d ((res σ)⁻¹) : ℚ) * ν e ∧
      (∃ eσ : Qbar,
        ProjectivelyEqual (P σ) (parameterTriple s eσ)) ∧
      (∀ eσ : Qbar,
        ProjectivelyEqual (P σ) (parameterTriple s eσ) →
          (eσ = σ e ∨ eσ = -(σ e)) ∧
          ν eσ = (d ((res σ)⁻¹) : ℚ) * ν e) := by
  have he0 : e ≠ 0 := by
    intro h
    have hh := hRadialDilation_unit 1
    simp [h] at hh
  have he₀0 : e₀ ≠ 0 := by
    intro h
    rcases hSphericalAction_parameter with he | he <;> simp [h] at he <;> exact he0 he
  have hd1 : d 1 = 1 := by
    rw [hLefschetzNormalization_sign, inv_one, hLefschetzNormalization_normalized]
    rfl
  have hrootvals (σ : Gal(Qbar/ℚ)) :
      ν (σ e₀) = -(ε : ℚ) * 3 / 2 * (d ((res σ)⁻¹) : ℚ) :=
    dilation_root_valuation ιE res hres (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
      (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_ne_one E) (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E) d
      (inverse_sign_odd E v d hLefschetzNormalization_sign) reps hLefschetzNormalization_representatives
      r M hM ν hν_mul hsplit e₀ ω ζ he₀0 ε hRadialDilation_phase
      hRadialDilation_relation hSphericalAction_root σ
  have hbase : ν e₀ = -(ε : ℚ) * 3 / 2 := by
    simpa only [map_one, inv_one, hd1, Int.cast_one, mul_one, AlgEquiv.one_apply]
      using hrootvals 1
  have hbase_sign : ν e₀ = (-3 / 2 : ℚ) ∨ ν e₀ = (3 / 2 : ℚ) := by
    rcases hRadialDilation_convention with h | h <;> norm_num [hbase, h]
  have hroot_sign (σ : Gal(Qbar/ℚ)) :
      ν (σ e₀) = (d ((res σ)⁻¹) : ℚ) * ν e₀ := by
    rw [hrootvals, hbase]
    ring
  have he_sign : (ν e = (-3 / 2 : ℚ) ∨ ν e = (3 / 2 : ℚ)) ∧
      ∀ σ : Gal(Qbar/ℚ), ν (σ e) = (d ((res σ)⁻¹) : ℚ) * ν e := by
    rcases hSphericalAction_parameter with he | he
    · exact he ▸ ⟨hbase_sign, hroot_sign⟩
    · rw [he, val_inv ν hν_mul e₀ he₀0]
      constructor
      · rcases hbase_sign with h | h
        · right; rw [h]; norm_num
        · left; rw [h]; norm_num
      · intro σ
        rw [map_inv₀, val_inv ν hν_mul _ ((map_ne_zero σ).mpr he₀0), hroot_sign]
        ring
  refine ⟨he_sign.1, ?_⟩
  intro σ
  refine ⟨he_sign.2 σ, ?_, ?_⟩
  · obtain ⟨eσ, hnormσ⟩ := normalize_conjugate_triple q s e hs σ
    exact ⟨eσ, projective_trans (hRationalStructure σ) hnormσ⟩
  · intro eσ heσ
    have hσsq : (σ s) ^ 2 = (q : Qbar) := by rw [← map_pow, hs, map_natCast]
    have hp := projective_trans (projective_symm heσ) (hRationalStructure σ)
    rw [conjugate_triple] at hp
    have hchoice := projective_parameter_unique q hq s (σ s) (σ e) eσ
      hs hσsq j (hRadialDilation_unit σ) hp
    refine ⟨hchoice, ?_⟩
    rcases hchoice with h | h
    · rw [h, he_sign.2 σ]
    · rw [h, val_neg ν hν_mul _ ((map_ne_zero σ).mpr he0), he_sign.2 σ]

end

end OAI.RepresentationTheory.Hecke.GaloisValuationCm
