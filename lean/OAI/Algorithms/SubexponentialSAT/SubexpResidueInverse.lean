import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialCost
import OAI.Algorithms.SubexponentialSAT.SubexpActualRing
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Executable inversion by finite-field powering and nilpotent correction

The algorithm uses only scalar additions and multiplications, with explicit
finite loops. It constructs the entire inverse-difference table needed by CRT.
Its counters are ring-operation counts, not an assertion of machine time.
-/

namespace SubexponentialSAT.SubexpResidueInverse

open scoped BigOperators

section Algorithm

variable {A : Type*} [CommRing A]

/-- A shared Horner recurrence for the finite geometric sum. -/
def geometricHornerWithCost (z : A) : ℕ → A × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let previous := geometricHornerWithCost z n
      (z * previous.1 + 1, previous.2 + 2)

theorem geometricHorner_value (z : A) (n : ℕ) :
    (geometricHornerWithCost z n).1 = ∑ i ∈ Finset.range n, z ^ i := by
  induction n with
  | zero => simp [geometricHornerWithCost]
  | succ n ih => simpa [geometricHornerWithCost, ih] using (@geom_sum_succ A _ z n).symm

@[simp] theorem geometricHorner_cost (z : A) (n : ℕ) :
    (geometricHornerWithCost z n).2 = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [geometricHornerWithCost, ih]; omega

/-- Power to `q-2`, then correct the nilpotent defect. Negation is implemented
as multiplication by the fixed constant `-1`, and is included in the count. -/
def inverseWithCost (q μ : ℕ) (a : A) : A × ℕ :=
  let b := SubexpPolynomialCost.scalarPowerWithCost a (q - 2)
  let ab := a * b.1
  let negab := (-1 : A) * ab
  let z := negab + 1
  let g := geometricHornerWithCost z μ
  (b.1 * g.1, b.2 + 3 + g.2 + 1)

theorem inverseWithCost_value (q μ : ℕ) (a : A) :
    (inverseWithCost q μ a).1 =
      NilpotentDefect.geometricInverse a (a ^ (q - 2)) μ := by
  simp only [inverseWithCost, SubexpPolynomialCost.scalarPower_value,
    geometricHorner_value, NilpotentDefect.geometricInverse]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

@[simp] theorem inverseWithCost_cost_eq (q μ : ℕ) (a : A) :
    (inverseWithCost q μ a).2 = (q - 2) + 2 * μ + 4 := by
  simp only [inverseWithCost, SubexpPolynomialCost.scalarPower_cost, geometricHorner_cost]
  omega

theorem inverseWithCost_cost (q μ : ℕ) (a : A) :
    (inverseWithCost q μ a).2 ≤ q + 2 * μ + 4 := by
  rw [inverseWithCost_cost_eq]
  omega

/-- Diagonal table entries are zero. Off-diagonal subtraction costs one
multiplication by `-1` and one addition before inversion. -/
def differenceInverseWithCost {Q : ℕ} (θ : Fin Q → A) (q μ : ℕ)
    (i j : Fin Q) : A × ℕ :=
  if i = j then (0, 0) else
    let negj := (-1 : A) * θ j
    let a := θ i + negj
    let result := inverseWithCost q μ a
    (result.1, 2 + result.2)

@[simp] theorem differenceInverseWithCost_diag {Q : ℕ} (θ : Fin Q → A)
    (q μ : ℕ) (i : Fin Q) : differenceInverseWithCost θ q μ i i = (0, 0) := by
  simp [differenceInverseWithCost]

theorem differenceInverseWithCost_value {Q : ℕ} (θ : Fin Q → A) (q μ : ℕ)
    (i j : Fin Q) (hij : i ≠ j) :
    (differenceInverseWithCost θ q μ i j).1 = (inverseWithCost q μ (θ i - θ j)).1 := by
  simp [differenceInverseWithCost, hij, sub_eq_add_neg]

theorem differenceInverseWithCost_cost {Q : ℕ} (θ : Fin Q → A) (q μ : ℕ)
    (i j : Fin Q) :
    (differenceInverseWithCost θ q μ i j).2 ≤ q + 2 * μ + 6 := by
  unfold differenceInverseWithCost
  split
  · simp
  · dsimp only
    have := inverseWithCost_cost q μ (θ i + (-1 : A) * θ j)
    omega

/-- Materialize all entries once, in a finite array of finite arrays. -/
def inverseTableWithCost {Q : ℕ} (θ : Fin Q → A) (q μ : ℕ) :
    List.Vector (List.Vector A Q) Q × ℕ :=
  let entries := List.Vector.ofFn (fun i =>
    List.Vector.ofFn (fun j => differenceInverseWithCost θ q μ i j))
  (entries.map (fun row => row.map Prod.fst),
    (entries.toList.map (fun row => (row.toList.map Prod.snd).sum)).sum)

@[simp] theorem inverseTableWithCost_entry {Q : ℕ} (θ : Fin Q → A) (q μ : ℕ)
    (i j : Fin Q) :
    (((inverseTableWithCost θ q μ).1.get i).get j) =
      (differenceInverseWithCost θ q μ i j).1 := by
  simp [inverseTableWithCost]

theorem inverseTableWithCost_cost {Q : ℕ} (θ : Fin Q → A) (q μ : ℕ) :
    (inverseTableWithCost θ q μ).2 ≤ Q ^ 2 * (q + 2 * μ + 6) := by
  simp only [inverseTableWithCost, List.Vector.toList_ofFn, List.map_ofFn,
    Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin Q, ∑ _j : Fin Q, (q + 2 * μ + 6) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => differenceInverseWithCost_cost θ q μ i j)
    _ = Q ^ 2 * (q + 2 * μ + 6) := by simp; ring

end Algorithm

section Correctness

variable {A E : Type*} [CommRing A] [Field E] [Fintype E]

/-- A finite-field Fermat power is an inverse after reduction. -/
theorem residue_fermat_inverse (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (a : A) (ha : ρ a ≠ 0) :
    ρ (a * a ^ (q - 2)) = 1 := by
  have hq2 : 2 ≤ q := by
    rw [← hq]
    exact Fintype.one_lt_card
  rw [map_mul, map_pow, ← pow_succ']
  have he : q - 2 + 1 = q - 1 := by omega
  rw [he, ← hq]
  exact FiniteField.pow_card_sub_one_eq_one (ρ a) ha

/-- The principal-kernel condition converts the residue defect into a
nilpotent element of the original, possibly non-field ring. -/
theorem fermat_defect_nilpotent (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x) (a : A) (ha : ρ a ≠ 0) :
    (1 - a * a ^ (q - 2)) ^ μ = 0 := by
  have hz : ρ (1 - a * a ^ (q - 2)) = 0 := by
    rw [map_sub, map_one, residue_fermat_inverse ρ q hq a ha, sub_self]
  obtain ⟨d, hd⟩ := hker _ hz
  rw [hd, mul_pow, hπ, zero_mul]

theorem inverseWithCost_correct (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x) (a : A) (ha : ρ a ≠ 0) :
    (inverseWithCost q μ a).1 * a = 1 := by
  rw [inverseWithCost_value]
  exact NilpotentDefect.geometricInverse_mul a (a ^ (q - 2)) μ
    (fermat_defect_nilpotent ρ q hq π μ hπ hker a ha)

theorem inverseWithCost_spec (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x) (a : A) (ha : ρ a ≠ 0) :
    (inverseWithCost q μ a).1 * a = 1 ∧
      (inverseWithCost q μ a).2 ≤ q + 2 * μ + 4 :=
  ⟨inverseWithCost_correct ρ q hq π μ hπ hker a ha, inverseWithCost_cost q μ a⟩

theorem inverseWithCost_correct_of_kernel_eq (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : RingHom.ker ρ = Ideal.span ({π} : Set A)) (a : A) (ha : ρ a ≠ 0) :
    (inverseWithCost q μ a).1 * a = 1 := by
  apply inverseWithCost_correct ρ q hq π μ hπ _ a ha
  intro x hx
  have hm : x ∈ RingHom.ker ρ := hx
  rw [hker, Ideal.mem_span_singleton] at hm
  exact hm

theorem inverseTableWithCost_correct {Q : ℕ} (θ : Fin Q → A) (ρ : A →+* E)
    (q : ℕ) (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hθ : Function.Injective (fun i => ρ (θ i)))
    (i j : Fin Q) (hij : i ≠ j) :
    (((inverseTableWithCost θ q μ).1.get i).get j) * (θ i - θ j) = 1 := by
  rw [inverseTableWithCost_entry, differenceInverseWithCost_value θ q μ i j hij]
  apply inverseWithCost_correct ρ q hq π μ hπ hker
  rw [map_sub, sub_ne_zero]
  exact fun h => hij (hθ h)

end Correctness

section CompleteCRT

variable {A E : Type*} [CommRing A] [Field E] [Fintype E]

/-- Complete preprocessing and reconstruction from residue-distinct nodes.
The supplied data contain no inverse elements. -/
def crtFromResiduesWithCost {Q : ℕ} (θ : Fin Q → A) (q μ D : ℕ)
    (J : Fin Q → List A) : List A × ℕ :=
  let table := inverseTableWithCost θ q μ
  let result := SubexpPolynomialCost.crtFromDifferences θ D
    (fun i j => (table.1.get i).get j) J
  (result.1, table.2 + result.2)

theorem crtFromResiduesWithCost_cost {Q : ℕ} (θ : Fin Q → A) (q μ D : ℕ)
    (J : Fin Q → List A) (hJ : ∀ i, (J i).length ≤ D) :
    (crtFromResiduesWithCost θ q μ D J).2 ≤
      Q ^ 2 * (q + 2 * μ + 6) + 129 * (Q + 1) ^ 3 * (D + 1) ^ 4 := by
  exact Nat.add_le_add (inverseTableWithCost_cost θ q μ)
    (SubexpPolynomialCost.crtFromDifferences_cost θ D _ J hJ)

/-- For all nonzero residue-field nodes and `μ = D+1`, the entire inverse
preparation is absorbed by a fixed polynomial in the displayed CRT sizes. -/
theorem crtFromResiduesWithCost_fullNodeCost {Q : ℕ} (θ : Fin Q → A) (D : ℕ)
    (J : Fin Q → List A) (hJ : ∀ i, (J i).length ≤ D) :
    (crtFromResiduesWithCost θ (Q + 1) (D + 1) D J).2 ≤
      140 * (Q + 1) ^ 3 * (D + 1) ^ 4 := by
  apply (crtFromResiduesWithCost_cost θ (Q + 1) (D + 1) D J hJ).trans
  ring_nf
  omega

theorem crtFromResiduesWithCost_correct {Q : ℕ} [NeZero Q]
    (θ : Fin Q → A) (ρ : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (π : A) (μ : ℕ) (hπ : π ^ μ = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hθ : Function.Injective (fun i => ρ (θ i)))
    (D : ℕ) (hD : 0 < D) (J : Fin Q → List A)
    (H : Polynomial A) (hH : H.natDegree < Q * D)
    (hjets : ∀ i, Truncation.trunc D (PolynomialAlgorithm.denote (J i)) =
      JetCRT.jet (θ i) D H)
    (hlength : ∀ i, (J i).length ≤ D) :
    PolynomialAlgorithm.denote (crtFromResiduesWithCost θ q μ D J).1 = H := by
  let _ : Nontrivial A := ρ.domain_nontrivial
  exact (SubexpPolynomialCost.crtFromDifferences_spec θ D hD _
    (inverseTableWithCost_correct θ ρ q hq π μ hπ hker hθ)
    J H hH hjets hlength).1

theorem crtFromResiduesWithCost_length {Q : ℕ} (θ : Fin Q → A) (q μ D : ℕ)
    (J : Fin Q → List A) :
    (crtFromResiduesWithCost θ q μ D J).1.length ≤ 4 * (Q + 1) * (D + 1) :=
  SubexpPolynomialCost.crtFromDifferences_length θ D _ J

end CompleteCRT

section Represented

variable {C A : Type*} [CommRing A]
    (ops : SubexpSymbolicCost.RepresentedRing C A)

/-- Shared powering over concrete coefficient routines. The counter is the
sum of counters returned by those routines, including the initial one. -/
def powerRun (a : C) : ℕ → C × ℕ
  | 0 => ops.oneRun
  | n + 1 =>
      let previous := powerRun a n
      let result := ops.mulRun previous.1 a
      (result.1, previous.2 + result.2)

theorem powerRun_value (a : C) (n : ℕ) :
    ops.decode (powerRun ops a n).1 = ops.decode a ^ n := by
  induction n with
  | zero => simpa [powerRun] using ops.one_correct
  | succ n ih => simp [powerRun, ops.mul_correct, ih, pow_succ]

/-- The value representing one is cached by the caller. -/
def hornerRun (one z : C) : ℕ → C × ℕ
  | 0 => ops.zeroRun
  | n + 1 =>
      let previous := hornerRun one z n
      let product := ops.mulRun z previous.1
      let result := ops.addRun product.1 one
      (result.1, previous.2 + product.2 + result.2)

theorem hornerRun_value (one z : C) (hone : ops.decode one = 1) (n : ℕ) :
    ops.decode (hornerRun ops one z n).1 =
      ∑ i ∈ Finset.range n, ops.decode z ^ i := by
  induction n with
  | zero => exact ops.zero_correct
  | succ n ih =>
      simpa [hornerRun, ops.add_correct, ops.mul_correct, hone, ih] using
        (@geom_sum_succ A _ (ops.decode z) n).symm

/-- Concrete coefficient inversion using the shared represented-ring API. -/
def inverseRun (q μ : ℕ) (a : C) : C × ℕ :=
  let b := powerRun ops a (q - 2)
  let ab := ops.mulRun a b.1
  let negab := ops.negRun ab.1
  let one := ops.oneRun
  let z := ops.addRun negab.1 one.1
  let g := hornerRun ops one.1 z.1 μ
  let result := ops.mulRun b.1 g.1
  (result.1, b.2 + ab.2 + negab.2 + one.2 + z.2 + g.2 + result.2)

theorem inverseRun_value (q μ : ℕ) (a : C) :
    ops.decode (inverseRun ops q μ a).1 =
      (inverseWithCost q μ (ops.decode a)).1 := by
  rw [inverseWithCost_value]
  simp only [inverseRun, ops.mul_correct, powerRun_value,
    hornerRun_value ops _ _ ops.one_correct, ops.add_correct, ops.neg_correct,
    ops.one_correct, NilpotentDefect.geometricInverse]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

def differenceInverseRun {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ)
    (i j : Fin Q) : C × ℕ :=
  if i = j then ops.zeroRun else
    let negj := ops.negRun (θ j)
    let a := ops.addRun (θ i) negj.1
    let result := inverseRun ops q μ a.1
    (result.1, negj.2 + a.2 + result.2)

theorem differenceInverseRun_value {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ)
    (i j : Fin Q) :
    ops.decode (differenceInverseRun ops θ q μ i j).1 =
      (differenceInverseWithCost (fun k => ops.decode (θ k)) q μ i j).1 := by
  by_cases hij : i = j
  · simp [differenceInverseRun, differenceInverseWithCost, hij, ops.zero_correct]
  · simp [differenceInverseRun, differenceInverseWithCost, hij, inverseRun_value,
      ops.add_correct, ops.neg_correct]

def inverseTableRun {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ) :
    List.Vector (List.Vector C Q) Q × ℕ :=
  let entries := List.Vector.ofFn (fun i =>
    List.Vector.ofFn (fun j => differenceInverseRun ops θ q μ i j))
  (entries.map (fun row => row.map Prod.fst),
    (entries.toList.map (fun row => (row.toList.map Prod.snd).sum)).sum)

@[simp] theorem inverseTableRun_entry {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ)
    (i j : Fin Q) :
    (((inverseTableRun ops θ q μ).1.get i).get j) =
      (differenceInverseRun ops θ q μ i j).1 := by
  simp [inverseTableRun]

theorem inverseTableRun_value {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ)
    (i j : Fin Q) :
    ops.decode (((inverseTableRun ops θ q μ).1.get i).get j) =
      (((inverseTableWithCost (fun k => ops.decode (θ k)) q μ).1.get i).get j) := by
  rw [inverseTableRun_entry, inverseTableWithCost_entry, differenceInverseRun_value]

variable {B : ℕ} (budget : SubexpSymbolicCost.ScalarBudget ops B)

include budget

theorem powerRun_cost (a : C) (n : ℕ) :
    (powerRun ops a n).2 ≤ (n + 1) * B := by
  induction n with
  | zero => simpa [powerRun] using budget.one
  | succ n ih =>
      have hm := budget.mul (powerRun ops a n).1 a
      change (powerRun ops a n).2 + (ops.mulRun (powerRun ops a n).1 a).2 ≤ _
      calc
        _ ≤ (n + 1) * B + B := Nat.add_le_add ih hm
        _ = (n + 1 + 1) * B := by ring

theorem hornerRun_cost (one z : C) (n : ℕ) :
    (hornerRun ops one z n).2 ≤ (2 * n + 1) * B := by
  induction n with
  | zero => simpa [hornerRun] using budget.zero
  | succ n ih =>
      have hm := budget.mul z (hornerRun ops one z n).1
      have ha := budget.add (ops.mulRun z (hornerRun ops one z n).1).1 one
      change (hornerRun ops one z n).2 + (ops.mulRun z (hornerRun ops one z n).1).2 +
        (ops.addRun (ops.mulRun z (hornerRun ops one z n).1).1 one).2 ≤ _
      calc
        _ ≤ (2 * n + 1) * B + B + B := Nat.add_le_add (Nat.add_le_add ih hm) ha
        _ = (2 * (n + 1) + 1) * B := by ring

theorem inverseRun_cost (q μ : ℕ) (a : C) :
    (inverseRun ops q μ a).2 ≤ (q + 2 * μ + 7) * B := by
  let b := powerRun ops a (q - 2)
  let ab := ops.mulRun a b.1
  let negab := ops.negRun ab.1
  let z := ops.addRun negab.1 ops.oneRun.1
  let g := hornerRun ops ops.oneRun.1 z.1 μ
  have hb : b.2 ≤ (q + 1) * B :=
    (powerRun_cost ops budget a (q - 2)).trans (Nat.mul_le_mul_right B (by omega))
  have hab : ab.2 ≤ B := budget.mul _ _
  have hn : negab.2 ≤ B := budget.neg _
  have hz : z.2 ≤ B := budget.add _ _
  have hg : g.2 ≤ (2 * μ + 1) * B := hornerRun_cost ops budget _ _ μ
  have hr := budget.mul b.1 g.1
  have ho := budget.one
  change b.2 + ab.2 + negab.2 + ops.oneRun.2 + z.2 + g.2 + (ops.mulRun b.1 g.1).2 ≤ _
  calc
    _ ≤ (q + 1) * B + B + B + B + B + (2 * μ + 1) * B + B := by omega
    _ = (q + 2 * μ + 7) * B := by ring

theorem differenceInverseRun_cost {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ)
    (i j : Fin Q) :
    (differenceInverseRun ops θ q μ i j).2 ≤ (q + 2 * μ + 9) * B := by
  unfold differenceInverseRun
  split
  · calc
      _ ≤ B := budget.zero
      _ ≤ (q + 2 * μ + 9) * B := by
        simpa using Nat.mul_le_mul_right B (show 1 ≤ q + 2 * μ + 9 by omega)
  · have hn := budget.neg (θ j)
    have ha := budget.add (θ i) (ops.negRun (θ j)).1
    have hr := inverseRun_cost ops budget q μ (ops.addRun (θ i) (ops.negRun (θ j)).1).1
    dsimp only
    calc
      _ ≤ B + B + (q + 2 * μ + 7) * B := by omega
      _ = (q + 2 * μ + 9) * B := by ring

theorem inverseTableRun_cost {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ) :
    (inverseTableRun ops θ q μ).2 ≤ Q ^ 2 * (q + 2 * μ + 9) * B := by
  simp only [inverseTableRun, List.Vector.toList_ofFn, List.map_ofFn,
    Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin Q, ∑ _j : Fin Q, (q + 2 * μ + 9) * B := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => differenceInverseRun_cost ops budget θ q μ i j)
    _ = Q ^ 2 * (q + 2 * μ + 9) * B := by simp; ring

omit budget

variable {E : Type*} [Field E] [Fintype E]

theorem inverseRun_correct (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x) (a : C) (ha : ρ (ops.decode a) ≠ 0) :
    ops.decode (inverseRun ops q μ a).1 * ops.decode a = 1 := by
  rw [inverseRun_value]
  exact inverseWithCost_correct ρ q hq π μ hπ hker _ ha

theorem inverseTableRun_correct {Q : ℕ} (θ : Fin Q → C) (ρ : A →+* E)
    (q : ℕ) (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hθ : Function.Injective (fun i => ρ (ops.decode (θ i))))
    (i j : Fin Q) (hij : i ≠ j) :
    ops.decode (((inverseTableRun ops θ q μ).1.get i).get j) *
      (ops.decode (θ i) - ops.decode (θ j)) = 1 := by
  rw [inverseTableRun_value]
  exact inverseTableWithCost_correct _ ρ q hq π μ hπ hker hθ i j hij

end Represented

section Programs

variable {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)

def powerProgram (a : C) : ℕ → C × ℕ
  | 0 => ops.oneRun
  | n + 1 =>
      let previous := powerProgram a n
      let result := ops.mulRun previous.1 a
      (result.1, previous.2 + result.2)

def hornerProgram (one z : C) : ℕ → C × ℕ
  | 0 => ops.zeroRun
  | n + 1 =>
      let previous := hornerProgram one z n
      let product := ops.mulRun z previous.1
      let result := ops.addRun product.1 one
      (result.1, previous.2 + product.2 + result.2)

def inverseProgram (q μ : ℕ) (a : C) : C × ℕ :=
  let b := powerProgram ops a (q - 2)
  let ab := ops.mulRun a b.1
  let negab := ops.negRun ab.1
  let one := ops.oneRun
  let z := ops.addRun negab.1 one.1
  let g := hornerProgram ops one.1 z.1 μ
  let result := ops.mulRun b.1 g.1
  (result.1, b.2 + ab.2 + negab.2 + one.2 + z.2 + g.2 + result.2)

def differenceInverseProgram {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ)
    (i j : Fin Q) : C × ℕ :=
  if i = j then ops.zeroRun else
    let negj := ops.negRun (θ j)
    let a := ops.addRun (θ i) negj.1
    let result := inverseProgram ops q μ a.1
    (result.1, negj.2 + a.2 + result.2)

/-- The inverse table executed without carrying any semantic decoder. -/
def inverseTableProgram {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ) :
    List.Vector (List.Vector C Q) Q × ℕ :=
  let entries := List.Vector.ofFn (fun i =>
    List.Vector.ofFn (fun j => differenceInverseProgram ops θ q μ i j))
  (entries.map (fun row => row.map Prod.fst),
    (entries.toList.map (fun row => (row.toList.map Prod.snd).sum)).sum)

end Programs

section ProgramRefinement

variable {C A : Type*} [CommRing A] (ops : SubexpSymbolicCost.RepresentedRing C A)

@[simp] theorem powerProgram_run (a : C) (n : ℕ) :
    powerProgram ops.program a n = powerRun ops a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powerProgram, powerRun, ih]

@[simp] theorem hornerProgram_run (one z : C) (n : ℕ) :
    hornerProgram ops.program one z n = hornerRun ops one z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [hornerProgram, hornerRun, ih]

@[simp] theorem inverseProgram_run (q μ : ℕ) (a : C) :
    inverseProgram ops.program q μ a = inverseRun ops q μ a := by
  simp only [inverseProgram, inverseRun, powerProgram_run, hornerProgram_run]

@[simp] theorem differenceInverseProgram_run {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ)
    (i j : Fin Q) :
    differenceInverseProgram ops.program θ q μ i j = differenceInverseRun ops θ q μ i j := by
  simp only [differenceInverseProgram, differenceInverseRun, inverseProgram_run]

@[simp] theorem inverseTableProgram_run {Q : ℕ} (θ : Fin Q → C) (q μ : ℕ) :
    inverseTableProgram ops.program θ q μ = inverseTableRun ops θ q μ := by
  simp only [inverseTableProgram, inverseTableRun, differenceInverseProgram_run]

end ProgramRefinement

section SelectedQuartic

variable (p μ : ℕ) [Fact p.Prime]

theorem selectedQuartic_inverse (hμ : 0 < μ) (a : SubexpActualRing.Ring p μ)
    (ha : SubexpActualRing.rho p μ hμ a ≠ 0) :
    (inverseWithCost (p ^ 4) μ a).1 * a = 1 ∧
      (inverseWithCost (p ^ 4) μ a).2 ≤ p ^ 4 + 2 * μ + 4 :=
  inverseWithCost_spec (SubexpActualRing.rho p μ hμ) (p ^ 4)
    (SubexpActualRing.extension_card p) (p : SubexpActualRing.Ring p μ) μ
    (SubexpActualRing.prime_power_zero p μ)
    (fun x hx => (SubexpActualRing.rho_eq_zero_iff p μ hμ x).mp hx) a ha

theorem selectedQuartic_inverseTable {Q : ℕ} (hμ : 0 < μ)
    (θ : Fin Q → SubexpActualRing.Ring p μ)
    (hθ : Function.Injective (fun i => SubexpActualRing.rho p μ hμ (θ i))) :
    (∀ i j, i ≠ j →
      (((inverseTableWithCost θ (p ^ 4) μ).1.get i).get j) * (θ i - θ j) = 1) ∧
      (inverseTableWithCost θ (p ^ 4) μ).2 ≤ Q ^ 2 * (p ^ 4 + 2 * μ + 6) := by
  refine ⟨?_, inverseTableWithCost_cost θ (p ^ 4) μ⟩
  exact inverseTableWithCost_correct θ (SubexpActualRing.rho p μ hμ) (p ^ 4)
    (SubexpActualRing.extension_card p) (p : SubexpActualRing.Ring p μ) μ
    (SubexpActualRing.prime_power_zero p μ)
    (fun x hx => (SubexpActualRing.rho_eq_zero_iff p μ hμ x).mp hx) hθ

theorem selectedQuartic_inverseTableRun {C : Type*}
    (ops : SubexpSymbolicCost.RepresentedRing C (SubexpActualRing.Ring p μ))
    {B : ℕ} (budget : SubexpSymbolicCost.ScalarBudget ops B)
    {Q : ℕ} (hμ : 0 < μ) (θ : Fin Q → C)
    (hθ : Function.Injective (fun i => SubexpActualRing.rho p μ hμ (ops.decode (θ i)))) :
    (∀ i j, i ≠ j →
      ops.decode (((inverseTableRun ops θ (p ^ 4) μ).1.get i).get j) *
        (ops.decode (θ i) - ops.decode (θ j)) = 1) ∧
      (inverseTableRun ops θ (p ^ 4) μ).2 ≤ Q ^ 2 * (p ^ 4 + 2 * μ + 9) * B := by
  refine ⟨?_, inverseTableRun_cost ops budget θ (p ^ 4) μ⟩
  exact inverseTableRun_correct ops θ (SubexpActualRing.rho p μ hμ) (p ^ 4)
    (SubexpActualRing.extension_card p) (p : SubexpActualRing.Ring p μ) μ
    (SubexpActualRing.prime_power_zero p μ)
    (fun x hx => (SubexpActualRing.rho_eq_zero_iff p μ hμ x).mp hx) hθ

theorem selectedQuartic_CRT {Q : ℕ} [NeZero Q] (hμ : 0 < μ)
    (θ : Fin Q → SubexpActualRing.Ring p μ)
    (hθ : Function.Injective (fun i => SubexpActualRing.rho p μ hμ (θ i)))
    (D : ℕ) (hD : 0 < D) (J : Fin Q → List (SubexpActualRing.Ring p μ))
    (H : Polynomial (SubexpActualRing.Ring p μ)) (hH : H.natDegree < Q * D)
    (hjets : ∀ i, Truncation.trunc D (PolynomialAlgorithm.denote (J i)) =
      JetCRT.jet (θ i) D H)
    (hlength : ∀ i, (J i).length ≤ D) :
    PolynomialAlgorithm.denote (crtFromResiduesWithCost θ (p ^ 4) μ D J).1 = H ∧
      (crtFromResiduesWithCost θ (p ^ 4) μ D J).2 ≤
        Q ^ 2 * (p ^ 4 + 2 * μ + 6) + 129 * (Q + 1) ^ 3 * (D + 1) ^ 4 := by
  refine ⟨?_, crtFromResiduesWithCost_cost θ (p ^ 4) μ D J hlength⟩
  exact crtFromResiduesWithCost_correct θ (SubexpActualRing.rho p μ hμ) (p ^ 4)
    (SubexpActualRing.extension_card p) (p : SubexpActualRing.Ring p μ) μ
    (SubexpActualRing.prime_power_zero p μ)
    (fun x hx => (SubexpActualRing.rho_eq_zero_iff p μ hμ x).mp hx)
    hθ D hD J H hH hjets hlength

end SelectedQuartic

end SubexponentialSAT.SubexpResidueInverse

end OAI.Algorithms
