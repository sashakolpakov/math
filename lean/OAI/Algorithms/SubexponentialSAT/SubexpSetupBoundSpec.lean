import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

namespace OAI.Algorithms

/-!
# Measured bounds for composition of the concrete setup phases

The predicates below retain actual executions. Polynomial coefficients and
degrees are chosen before the input size and the incoming machine state.
-/

namespace SubexponentialSAT.SubexpSetupBoundSpec

open BitProgram StructuredCalls SubexpSetupStorage Filter

theorem wordBound_mono {r s B C : ℕ} {a : State r s}
    (ha : WordBound B a) (hBC : B ≤ C) : WordBound C a :=
  fun i => (ha i).trans hBC

/-- A fixed stack gains at most one bit per actual instruction. -/
theorem eval_wordBound {r s B t : ℕ} {cmd : Cmd r s} {a b : State r s}
    (ha : WordBound B a) (he : Eval cmd t a b) : WordBound (B + t) b := by
  intro i
  have hg := BitProgram.trace_selectedStackBits (compiled cmd i i) {i}
    (compiled_trace he i i)
  have hi : (b.stacks i).length ≤ (a.stacks i).length + t := by
    simpa only [BitProgram.selectedStackBits, Finset.sum_singleton,
      StructuredProgram.State.withPC] using hg
  exact hi.trans (Nat.add_le_add_right (ha i) t)

/-- A bounded witness bounds every execution of the same fixed command. -/
theorem bounds_of_witness {r s E t : ℕ} {cmd : Cmd r s} {a b : State r s}
    (port : Fin s)
    (hw : ∃ u out, Eval cmd u a out ∧ u ≤ E ∧ WordBound E out)
    (he : Eval cmd t a b) : t ≤ E ∧ WordBound E b := by
  obtain ⟨u, out, hu, htime, hword⟩ := hw
  have ht := SubexpPrimeProgram.eval_steps_unique he hu port port
  have hb := SubexpPrimeProgram.eval_result_unique he hu port port
  constructor
  · simpa only [ht] using htime
  · simpa only [hb] using hword

theorem input_le_polynomial (C d B : ℕ) (hC : 1 ≤ C) (hd : 1 ≤ d) :
    B ≤ C * (B + 1) ^ d := by
  have hp : B + 1 ≤ (B + 1) ^ d := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ B + 1) hd
  have hm := Nat.mul_le_mul_right ((B + 1) ^ d) hC
  simp only [one_mul] at hm
  omega

/-- The initial bound is a real bound on every stored word, not a declaration
that the eventual execution already has polynomial cost. -/
abbrev PolynomialRun {r s : ℕ} (cmd : Cmd r s)
    (pre post : ℕ → State r s → Prop) : Prop :=
  ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
    ∀ᶠ n : ℕ in atTop, ∀ B a, n ≤ B → pre n a → WordBound B a →
      ∃ t b, Eval cmd t a b ∧ t ≤ C * (B + 1) ^ d ∧
        WordBound (C * (B + 1) ^ d) b ∧ post n b

def PolynomialFunction (f : ℕ → ℕ) : Prop :=
  ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
    ∀ᶠ n : ℕ in atTop, f n ≤ C * (n + 1) ^ d

/-- Substitute a proved polynomial numerical-parameter bound into a local
execution envelope. Existence and cost remain separate checked premises. -/
theorem PolynomialRun.of_envelope {r s : ℕ} {cmd : Cmd r s}
    {pre post : ℕ → State r s → Prop} {P : ℕ → ℕ}
    (hP : PolynomialFunction P)
    (hsem : ∀ᶠ n : ℕ in atTop, ∀ a, pre n a →
      ∃ t b, Eval cmd t a b ∧ post n b)
    (hbound : ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧
      ∀ᶠ n : ℕ in atTop, ∀ B a t b,
        WordBound B a → pre n a → Eval cmd t a b →
          t ≤ C * (B + P n + 1) ^ q ∧ WordBound (C * (B + P n + 1) ^ q) b) :
    PolynomialRun cmd pre post := by
  obtain ⟨A, d, hA, hd, hP⟩ := hP
  obtain ⟨C, q, hC, hq, hbound⟩ := hbound
  refine ⟨C * (A + 1) ^ q, d * q, ?_, ?_, ?_⟩
  · have hp : 1 ≤ (A + 1) ^ q := Nat.one_le_pow _ _ (by omega)
    simpa only [one_mul] using Nat.mul_le_mul hC hp
  · simpa only [one_mul] using Nat.mul_le_mul hd hq
  filter_upwards [hP, hsem, hbound] with n hparam hsem hbound
  intro B a hn ha hw
  obtain ⟨t, b, he, hb⟩ := hsem a ha
  obtain ⟨ht, hword⟩ := hbound B a t b hw ha he
  have hparamB : P n ≤ A * (B + 1) ^ d := hparam.trans
    (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) d))
  have hbase : B + 1 ≤ (B + 1) ^ d := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ B + 1) hd
  have hinside : B + P n + 1 ≤ (A + 1) * (B + 1) ^ d := by
    calc
      B + P n + 1 = (B + 1) + P n := by omega
      _ ≤ (B + 1) ^ d + A * (B + 1) ^ d := Nat.add_le_add hbase hparamB
      _ = (A + 1) * (B + 1) ^ d := by ring
  have htotal : C * (B + P n + 1) ^ q ≤
      (C * (A + 1) ^ q) * (B + 1) ^ (d * q) := by
    calc
      C * (B + P n + 1) ^ q ≤ C * ((A + 1) * (B + 1) ^ d) ^ q :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinside q)
      _ = (C * (A + 1) ^ q) * (B + 1) ^ (d * q) := by
        rw [mul_pow, ← pow_mul]
        ring
  exact ⟨t, b, he, ht.trans htotal, wordBound_mono hword htotal, hb⟩

theorem PolynomialRun.mono {r s : ℕ} {cmd : Cmd r s}
    {pre pre' post post' : ℕ → State r s → Prop}
    (h : PolynomialRun cmd pre post)
    (hpre : ∀ n a, pre' n a → pre n a)
    (hpost : ∀ n a, post n a → post' n a) :
    PolynomialRun cmd pre' post' := by
  obtain ⟨C, d, hC, hd, h⟩ := h
  refine ⟨C, d, hC, hd, ?_⟩
  filter_upwards [h] with n hn
  intro B a hnB ha hw
  obtain ⟨t, b, he, ht, hword, hp⟩ := hn B a hnB (hpre n a ha) hw
  exact ⟨t, b, he, ht, hword, hpost n b hp⟩

theorem PolynomialRun.ite_true {r s : ℕ} {test : Fin r} {yes no : Cmd r s}
    {pre post : ℕ → State r s → Prop} (h : PolynomialRun yes pre post)
    (htest : ∀ n a, pre n a → a.regs test = true) :
    PolynomialRun (.ite test yes no) pre post := by
  obtain ⟨C, d, hC, hd, h⟩ := h
  refine ⟨C + 1, d, by omega, hd, ?_⟩
  filter_upwards [h] with n hn
  intro B a hnB ha hw
  obtain ⟨t, b, he, ht, hb, hp⟩ := hn B a hnB ha hw
  have hpow : 1 ≤ (B + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have htime : t + 1 ≤ (C + 1) * (B + 1) ^ d := by
    calc
      t + 1 ≤ C * (B + 1) ^ d + (B + 1) ^ d := Nat.add_le_add ht hpow
      _ = _ := by ring
  refine ⟨t + 1, b, .ite_true (htest n a ha) he, htime, ?_, hp⟩
  exact wordBound_mono hb (Nat.mul_le_mul_right _ (by omega))

/-- Polynomial measured executions compose with fixed coefficients and
degrees, while passing the actual intermediate state to the second phase. -/
theorem PolynomialRun.seq {r s : ℕ} {first second : Cmd r s}
    {pre middle post : ℕ → State r s → Prop}
    (hf : PolynomialRun first pre middle) (hs : PolynomialRun second middle post) :
    PolynomialRun (.seq first second) pre post := by
  obtain ⟨C, d, hC, hd, hf⟩ := hf
  obtain ⟨K, e, hK, he, hs⟩ := hs
  refine ⟨C + K * (C + 1) ^ e, d * e, by omega, ?_, ?_⟩
  · exact (by simpa using Nat.mul_le_mul hd he : 1 ≤ d * e)
  filter_upwards [hf, hs] with n hfirst hsecond
  intro B a hn ha hword
  obtain ⟨t, b, hrun, ht, hb, hmid⟩ := hfirst B a hn ha hword
  let F := C * (B + 1) ^ d
  have hnF : n ≤ F := hn.trans (input_le_polynomial C d B hC hd)
  obtain ⟨u, out, hurun, hu, hout, hpost⟩ := hsecond F b hnF hmid hb
  have hp : 1 ≤ (B + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hF : F + 1 ≤ (C + 1) * (B + 1) ^ d := by
    dsimp only [F]
    calc
      C * (B + 1) ^ d + 1 ≤ C * (B + 1) ^ d + (B + 1) ^ d :=
        Nat.add_le_add_left hp _
      _ = (C + 1) * (B + 1) ^ d := by ring
  have hsecondBound : K * (F + 1) ^ e ≤
      (K * (C + 1) ^ e) * (B + 1) ^ (d * e) := by
    calc
      K * (F + 1) ^ e ≤ K * ((C + 1) * (B + 1) ^ d) ^ e :=
        Nat.mul_le_mul_left K (Nat.pow_le_pow_left hF e)
      _ = (K * (C + 1) ^ e) * (B + 1) ^ (d * e) := by
        rw [mul_pow, ← pow_mul]
        ring
  have hde : d ≤ d * e := by
    simpa only [mul_one] using Nat.mul_le_mul_left d he
  have hfirstBound : C * (B + 1) ^ d ≤ C * (B + 1) ^ (d * e) :=
    Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) hde)
  have htotal : t + u ≤ (C + K * (C + 1) ^ e) * (B + 1) ^ (d * e) := by
    calc
      t + u ≤ C * (B + 1) ^ (d * e) +
          (K * (C + 1) ^ e) * (B + 1) ^ (d * e) :=
        Nat.add_le_add (ht.trans hfirstBound) (hu.trans hsecondBound)
      _ = _ := by ring
  refine ⟨t + u, out, .seq hrun hurun, htotal, ?_, hpost⟩
  apply wordBound_mono hout
  exact hsecondBound.trans (Nat.mul_le_mul_right _ (by omega))

end SubexponentialSAT.SubexpSetupBoundSpec

end OAI.Algorithms
