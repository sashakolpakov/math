import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Algorithm
import OAI.Algorithms.SubexponentialSAT.Truncation
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm

namespace OAI.Algorithms

/-!
# Explicit finite geometric inversion and local CRT factors

The inverses in this file are finite polynomial expressions. Scalar inverses are
input data with multiplication certificates; no Bézout coefficients are chosen.
-/

namespace SubexponentialSAT.TruncatedInverse

/-- A single-recursion loop retaining its current power and geometric sum.
Each iteration invokes its multiplication and addition functions once. -/
def geometricLoop {S : Type*} (zero one : S) (add mul : S → S → S) (z : S) :
    ℕ → S × S
  | 0 => (one, zero)
  | n + 1 =>
      let state := geometricLoop zero one add mul z n
      (mul state.1 z, add state.2 state.1)

/-- Semantic correctness requires only operation-preservation by `denote`;
the executable representation itself need not satisfy semiring equalities. -/
theorem geometricLoop_denote {S R : Type*} [Semiring R]
    (zero one : S) (add mul : S → S → S) (z : S) (denote : S → R)
    (hz : denote zero = 0) (ho : denote one = 1)
    (ha : ∀ x y, denote (add x y) = denote x + denote y)
    (hm : ∀ x y, denote (mul x y) = denote x * denote y) (n : ℕ) :
    denote (geometricLoop zero one add mul z n).1 = denote z ^ n ∧
      denote (geometricLoop zero one add mul z n).2 =
        ∑ j ∈ Finset.range n, denote z ^ j := by
  induction n with
  | zero => simp [geometricLoop, hz, ho]
  | succ n ih =>
      simp [geometricLoop, hm, ha, ih.1, ih.2, pow_succ, Finset.sum_range_succ]

/-- Instrument the same loop with the scalar-operation counters returned by
its concrete arithmetic routines. Previous states are evaluated once. -/
def geometricLoopWithCost {S : Type*} (zero one : S)
    (add mul : S → S → S × ℕ) (z : S) : ℕ → (S × S) × ℕ
  | 0 => ((one, zero), 0)
  | n + 1 =>
      let previous := geometricLoopWithCost zero one add mul z n
      let p := mul previous.1.1 z
      let s := add previous.1.2 previous.1.1
      ((p.1, s.1), previous.2 + p.2 + s.2)

theorem geometricLoopWithCost_value {S : Type*} (zero one : S)
    (add mul : S → S → S × ℕ) (z : S) (n : ℕ) :
    (geometricLoopWithCost zero one add mul z n).1 =
      geometricLoop zero one (fun x y => (add x y).1) (fun x y => (mul x y).1) z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [geometricLoopWithCost, geometricLoop, ih]

/-- The counter bound comes from the costs of the operations actually called
at each earlier state, rather than an annotation on the result. -/
theorem geometricLoopWithCost_cost_le {S : Type*} (zero one : S)
    (add mul : S → S → S × ℕ) (z : S) (n M B : ℕ)
    (hm : ∀ k < n, (mul (geometricLoopWithCost zero one add mul z k).1.1 z).2 ≤ M)
    (ha : ∀ k < n, (add (geometricLoopWithCost zero one add mul z k).1.2
      (geometricLoopWithCost zero one add mul z k).1.1).2 ≤ B) :
    (geometricLoopWithCost zero one add mul z n).2 ≤ n * (M + B) := by
  induction n with
  | zero => simp [geometricLoopWithCost]
  | succ n ih =>
      have hi := ih (fun k hk => hm k (Nat.lt_succ_of_lt hk))
        (fun k hk => ha k (Nat.lt_succ_of_lt hk))
      have hm' := hm n (Nat.lt_succ_self n)
      have ha' := ha n (Nat.lt_succ_self n)
      simp only [geometricLoopWithCost] at ⊢
      calc
        _ ≤ n * (M + B) + M + B := Nat.add_le_add (Nat.add_le_add hi hm') ha'
        _ = (n + 1) * (M + B) := by ring

/-- A uniform size bound for every stored power and partial geometric sum.
For dense polynomials, `size` is coefficient-list length. -/
theorem geometricLoop_size_le {S : Type*} (zero one : S) (add mul : S → S → S)
    (z : S) (size : S → ℕ) (hz : size zero ≤ 1) (ho : size one ≤ 1)
    (ha : ∀ x y, size (add x y) ≤ max (size x) (size y))
    (hm : ∀ x y, size (mul x y) ≤ size x + size y) (n : ℕ) :
    size (geometricLoop zero one add mul z n).1 ≤ 1 + n * size z ∧
      size (geometricLoop zero one add mul z n).2 ≤ 1 + n * size z := by
  induction n with
  | zero => simpa [geometricLoop] using And.intro ho hz
  | succ n ih =>
      constructor
      · change size (mul _ z) ≤ _
        calc
          _ ≤ size (geometricLoop zero one add mul z n).1 + size z := hm _ _
          _ ≤ (1 + n * size z) + size z := Nat.add_le_add_right ih.1 _
          _ = 1 + (n + 1) * size z := by ring
      · change size (add _ _) ≤ _
        calc
          _ ≤ max (size (geometricLoop zero one add mul z n).2)
            (size (geometricLoop zero one add mul z n).1) := ha _ _
          _ ≤ 1 + n * size z := max_le ih.2 ih.1
          _ ≤ 1 + (n + 1) * size z :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ n)) 1

section DenseAlgorithms

variable {A : Type*} [CommRing A]

/-- Dense coefficient-list implementation of the stored-power geometric loop. -/
def denseGeometricWithCost (z : List A) (D : ℕ) : (List A × List A) × ℕ :=
  geometricLoopWithCost [] [1] PolynomialAlgorithm.addWithCost PolynomialAlgorithm.mulWithCost z D

/-- The scalar inverse `a` is supplied explicitly. Its negation is computed
by one counted multiplication, and all polynomial operations are list routines. -/
def denseInverseWithCost (B : List A) (a : A) (D : ℕ) : List A × ℕ :=
  let negA := (-1) * a
  let scaled := PolynomialAlgorithm.scaleWithCost negA B
  let z := PolynomialAlgorithm.addWithCost [1] scaled.1
  let geometric := denseGeometricWithCost z.1 D
  let result := PolynomialAlgorithm.scaleWithCost a geometric.1.2
  (PolynomialAlgorithm.truncate D result.1, 1 + scaled.2 + z.2 + geometric.2 + result.2)

def denseCorrectionWithCost (B J : List A) (a : A) (D : ℕ) : List A × ℕ :=
  let inv := denseInverseWithCost B a D
  let result := PolynomialAlgorithm.mulWithCost J inv.1
  (PolynomialAlgorithm.truncate D result.1, inv.2 + result.2)

/-- Build the repeated linear factors with one counted negation multiplication
per retained node. Repeated factors reuse the computed coefficient. -/
def denseFactorsWithCost {I : Type*} [DecidableEq I]
    (θ : I → A) (D : ℕ) (i : I) : List I → List (List A) × ℕ
  | [] => ([], 0)
  | j :: js =>
      let rest := denseFactorsWithCost θ D i js
      if j = i then rest
      else
        let neg := (-1) * θ j
        (List.replicate D [neg, 1] ++ rest.1, rest.2 + 1)

theorem denseFactors_length {I : Type*} [DecidableEq I]
    (θ : I → A) (D : ℕ) (i : I) (js : List I) :
    (denseFactorsWithCost θ D i js).1.length ≤ js.length * D := by
  induction js with
  | nil => simp [denseFactorsWithCost]
  | cons j js ih =>
      by_cases h : j = i
      · simp only [denseFactorsWithCost, h, ↓reduceIte, List.length_cons]
        exact ih.trans (Nat.mul_le_mul_right D (Nat.le_succ js.length))
      · simp only [denseFactorsWithCost, h, ↓reduceIte, List.length_append,
          List.length_replicate, List.length_cons]
        calc
          _ ≤ D + js.length * D := Nat.add_le_add_left ih _
          _ = (js.length + 1) * D := by ring

theorem denseFactors_cost {I : Type*} [DecidableEq I]
    (θ : I → A) (D : ℕ) (i : I) (js : List I) :
    (denseFactorsWithCost θ D i js).2 ≤ js.length := by
  induction js with
  | nil => simp [denseFactorsWithCost]
  | cons j js ih =>
      by_cases h : j = i <;> simp only [denseFactorsWithCost, h, ↓reduceIte,
        List.length_cons] <;> omega

theorem denseFactors_each_length {I : Type*} [DecidableEq I]
    (θ : I → A) (D : ℕ) (i : I) (js : List I) :
    ∀ P ∈ (denseFactorsWithCost θ D i js).1, P.length ≤ 2 := by
  induction js with
  | nil => simp [denseFactorsWithCost]
  | cons j js ih =>
      by_cases h : j = i
      · simpa only [denseFactorsWithCost, h, ↓reduceIte] using ih
      · intro P hP
        simp only [denseFactorsWithCost, h, ↓reduceIte, List.mem_append] at hP
        rcases hP with hp | hp
        · have heq := (List.mem_replicate.mp hp).2
          subst P
          simp
        · exact ih P hp

def denseCofactorWithCost {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (i : Fin Q) : List A × ℕ :=
  let factors := denseFactorsWithCost θ D i (List.ofFn id)
  let product := PolynomialAlgorithm.productWithCost factors.1
  (product.1, factors.2 + product.2)

/-- One CRT summand. Every computed polynomial is bound once and reused. -/
def denseTermWithCost {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) (i : Fin Q) : List A × ℕ :=
  let cofactor := denseCofactorWithCost θ D i
  let shifted := PolynomialAlgorithm.shiftWithCost (θ i) cofactor.1
  let corrected := denseCorrectionWithCost shifted.1 (J i) (a i) D
  let negNode := (-1) * θ i
  let unshifted := PolynomialAlgorithm.shiftWithCost negNode corrected.1
  let result := PolynomialAlgorithm.mulWithCost cofactor.1 unshifted.1
  (result.1, cofactor.2 + shifted.2 + corrected.2 + 1 + unshifted.2 + result.2)

/-- The complete dense-list CRT loop, including the costs of every term and
the final coefficient-wise summation. Scalar inverse inputs `a` are explicit. -/
def denseCRTWithCost {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) : List A × ℕ :=
  let terms := List.ofFn (fun i => denseTermWithCost θ D a J i)
  let result := PolynomialAlgorithm.sumWithCost (terms.map Prod.fst)
  (result.1, (terms.map Prod.snd).sum + result.2)

/-- Explicit polynomials bounding the sizes and counters in the CRT loop. -/
def cofactorLength (Q D : ℕ) : ℕ := 1 + 2 * (Q * D)

def cofactorCost (Q D : ℕ) : ℕ := Q + 4 * (Q * D) * (1 + 2 * (Q * D))

def inverseCost (D L : ℕ) : ℕ :=
  L + 2 + D * (2 * (1 + D * L) * L + (1 + D * L)) + (1 + D * L)

def termLength (Q D : ℕ) : ℕ := cofactorLength Q D + 2 * D

def termCost (Q D : ℕ) : ℕ :=
  cofactorCost Q D + 5 * cofactorLength Q D ^ 2 +
    (inverseCost D (2 * cofactorLength Q D) + 2 * D * D) + 1 +
    5 * D ^ 2 + 4 * cofactorLength Q D * D

def crtCost (Q D : ℕ) : ℕ := Q * (termCost Q D + termLength Q D)

end DenseAlgorithms

end SubexponentialSAT.TruncatedInverse

noncomputable section

namespace SubexponentialSAT.TruncatedInverse

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

theorem trunc_degree_lt (D : ℕ) (f : A[X]) :
    (Truncation.trunc D f).degree < (D : ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).2
  intro n hn
  simp [Truncation.coeff_trunc, Nat.not_lt.mpr hn]

theorem X_pow_dvd_sub_trunc (D : ℕ) (f : A[X]) :
    (X : A[X]) ^ D ∣ f - Truncation.trunc D f := by
  rw [X_pow_dvd_iff]
  intro n hn
  simp [Truncation.coeff_trunc, hn]

/-- Coefficient truncation and monic remainder are the same operation. -/
theorem trunc_eq_modByMonic (D : ℕ) (f : A[X]) :
    Truncation.trunc D f = f %ₘ (X ^ D) := by
  nontriviality A
  have hself : Truncation.trunc D f %ₘ (X ^ D) = Truncation.trunc D f := by
    apply (modByMonic_eq_self_iff (monic_X.pow D)).2
    rw [degree_X_pow]
    exact trunc_degree_lt D f
  exact ((modByMonic_eq_of_dvd_sub (monic_X.pow D)
    (X_pow_dvd_sub_trunc D f)).trans hself).symm

theorem jet_eq_trunc (a : A) (D : ℕ) (f : A[X]) :
    JetCRT.jet a D f = Truncation.trunc D (f.comp (X + C a)) :=
  (trunc_eq_modByMonic D _).symm

@[simp] theorem trunc_idempotent (D : ℕ) (f : A[X]) :
    Truncation.trunc D (Truncation.trunc D f) = Truncation.trunc D f := by
  ext n
  by_cases hn : n < D <;> simp [Truncation.coeff_trunc, hn]

@[simp] theorem jet_modByMonic (a : A) (D : ℕ) (f : A[X]) :
    JetCRT.jet a D f %ₘ (X ^ D) = JetCRT.jet a D f := by
  rw [jet_eq_trunc, ← trunc_eq_modByMonic, trunc_idempotent]

/-- The untruncated finite geometric inverse expression. -/
def rawInverse (B : A[X]) (a : A) (D : ℕ) : A[X] :=
  C a * ∑ j ∈ Finset.range D, (1 - C a * B) ^ j

/-- The inverse represented by exactly its first `D` coefficients. -/
def inverse (B : A[X]) (a : A) (D : ℕ) : A[X] :=
  Truncation.trunc D (rawInverse B a D)

theorem rawInverse_correct (B : A[X]) (a : A) (D : ℕ)
    (ha : a * B.coeff 0 = 1) :
    (X : A[X]) ^ D ∣ B * rawInverse B a D - 1 := by
  let z : A[X] := 1 - C a * B
  have hz : (X : A[X]) ∣ z := by
    apply X_dvd_iff.mpr
    simp [z, coeff_sub, ha]
  have heq : B * rawInverse B a D - 1 = -(z ^ D) := by
    calc
      B * rawInverse B a D - 1 =
          (1 - z) * (∑ j ∈ Finset.range D, z ^ j) - 1 := by
        dsimp [rawInverse, z]
        ring
      _ = -(z ^ D) := by rw [mul_neg_geom_sum]; ring
  rw [heq]
  exact dvd_neg.mpr (pow_dvd_pow_of_dvd hz D)

/-- Only the supplied constant inverse is used. This works in positive
characteristic and in rings with zero divisors. -/
theorem inverse_correct (B : A[X]) (a : A) (D : ℕ)
    (ha : a * B.coeff 0 = 1) :
    (X : A[X]) ^ D ∣ B * inverse B a D - 1 := by
  have hraw := rawInverse_correct B a D ha
  have htail := dvd_mul_of_dvd_right (X_pow_dvd_sub_trunc D (rawInverse B a D)) B
  convert dvd_sub hraw htail using 1
  dsimp [inverse]
  ring

theorem inverse_degree_lt (B : A[X]) (a : A) (D : ℕ) :
    (inverse B a D).degree < (D : ℕ) :=
  trunc_degree_lt D _

/-- Multiply a jet by the inverse, keeping precisely the local order. -/
def correctedJet (B J : A[X]) (a : A) (D : ℕ) : A[X] :=
  Truncation.trunc D (J * inverse B a D)

theorem correctedJet_correct (B J : A[X]) (a : A) (D : ℕ)
    (ha : a * B.coeff 0 = 1) :
    (X : A[X]) ^ D ∣ B * correctedJet B J a D - J := by
  have hinv := dvd_mul_of_dvd_right (inverse_correct B a D ha) J
  have htail := dvd_mul_of_dvd_right (X_pow_dvd_sub_trunc D (J * inverse B a D)) B
  convert dvd_sub hinv htail using 1
  dsimp [correctedJet]
  ring

theorem local_dvd_iff (a : A) (D : ℕ) (f : A[X]) :
    (X : A[X]) ^ D ∣ f.comp (X + C a) ↔ JetCRT.nodePower a D ∣ f := by
  rw [dvd_comp_X_add_C_iff]
  simp only [JetCRT.nodePower, pow_comp, X_comp]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The other nodes' factors, expressed in node `i`'s local coordinate. -/
def localFactor (θ : ι → A) (D : ℕ) (i : ι) : A[X] :=
  (JetCRT.cofactor θ D i).comp (X + C (θ i))

def correction (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X]) (i : ι) : A[X] :=
  correctedJet (localFactor θ D i) (J i) (a i) D

/-- Explicit Hermite reconstruction. Local corrections are truncated before
shifting back, so no final polynomial division is required. -/
def reconstruct (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X]) : A[X] :=
  ∑ i, JetCRT.cofactor θ D i * (correction θ D a J i).comp (X - C (θ i))

theorem diagonal_correct (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X])
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1) (i : ι) :
    JetCRT.nodePower (θ i) D ∣
      JetCRT.cofactor θ D i * (correction θ D a J i).comp (X - C (θ i)) -
        (J i).comp (X - C (θ i)) := by
  apply (local_dvd_iff (θ i) D _).1
  simpa only [sub_comp, mul_comp, comp_assoc, X_comp, C_comp,
    add_sub_cancel_right, comp_X, correction, localFactor] using
      correctedJet_correct (localFactor θ D i) (J i) (a i) D (ha i)

theorem reconstruct_local_dvd (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X])
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1) (i : ι) :
    JetCRT.nodePower (θ i) D ∣ reconstruct θ D a J - (J i).comp (X - C (θ i)) := by
  unfold reconstruct
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_assoc]
  apply dvd_add
  · apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left
      (JetCRT.nodePower_dvd_cofactor θ D (Finset.mem_erase.mp hj).1.symm) _
  · exact diagonal_correct θ D a J ha i

theorem reconstruct_jets (θ : ι → A) (D : ℕ) (a : ι → A) (J : ι → A[X])
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1) (i : ι) :
    JetCRT.jet (θ i) D (reconstruct θ D a J) = Truncation.trunc D (J i) := by
  calc
    JetCRT.jet (θ i) D (reconstruct θ D a J) =
        JetCRT.jet (θ i) D ((J i).comp (X - C (θ i))) :=
      (JetCRT.jet_eq_iff_dvd_sub _ _ _ _).2 (reconstruct_local_dvd θ D a J ha i)
    _ = J i %ₘ (X ^ D) := JetCRT.jet_unshift _ _ _
    _ = Truncation.trunc D (J i) := (trunc_eq_modByMonic D _).symm

theorem trunc_natDegree_lt (D : ℕ) (hD : 0 < D) (f : A[X]) :
    (Truncation.trunc D f).natDegree < D := by
  by_cases h : Truncation.trunc D f = 0
  · simpa [h] using hD
  · exact (natDegree_lt_iff_degree_lt h).2 (trunc_degree_lt D f)

theorem cofactor_natDegree [Nontrivial A] (θ : ι → A) (D : ℕ) (i : ι) :
    (JetCRT.cofactor θ D i).natDegree = (Fintype.card ι - 1) * D := by
  rw [JetCRT.cofactor, natDegree_prod_of_monic _ _
    (fun j _ => JetCRT.nodePower_monic (θ j) D)]
  simp only [JetCRT.nodePower, (monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
  simp

theorem reconstruct_natDegree_lt [Nontrivial A] [Nonempty ι]
    (θ : ι → A) (D : ℕ) (hD : 0 < D) (a : ι → A) (J : ι → A[X]) :
    (reconstruct θ D a J).natDegree < Fintype.card ι * D := by
  have ht (i : ι) :
      (JetCRT.cofactor θ D i * (correction θ D a J i).comp (X - C (θ i))).natDegree ≤
        (Fintype.card ι - 1) * D + (D - 1) := by
    apply natDegree_mul_le.trans
    apply Nat.add_le_add
    · exact (cofactor_natDegree θ D i).le
    · have hc : (correction θ D a J i).natDegree < D :=
        trunc_natDegree_lt D hD _
      have hs := natDegree_comp_le (p := correction θ D a J i) (q := X - C (θ i))
      rw [natDegree_X_sub_C, mul_one] at hs
      exact hs.trans (by omega)
  have hb : (reconstruct θ D a J).natDegree ≤
      (Fintype.card ι - 1) * D + (D - 1) := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact ht i
  apply hb.trans_lt
  calc
    (Fintype.card ι - 1) * D + (D - 1) < (Fintype.card ι - 1) * D + D :=
      Nat.add_lt_add_left (Nat.sub_lt hD (by decide)) _
    _ = ((Fintype.card ι - 1) + 1) * D := by ring
    _ = Fintype.card ι * D := by rw [Nat.sub_add_cancel Fintype.card_pos]

/-- Correct local data reconstruct the original polynomial by the proved
degree bound and CRT injectivity, using the explicit geometric formula. -/
theorem reconstruct_eq [Nontrivial A] [Nonempty ι]
    (θ : ι → A) (D : ℕ) (hD : 0 < D)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j)) (a : ι → A) (J : ι → A[X])
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1)
    (H : A[X]) (hH : H.natDegree < Fintype.card ι * D)
    (hJ : ∀ i, Truncation.trunc D (J i) = JetCRT.jet (θ i) D H) :
    reconstruct θ D a J = H := by
  exact JetCRT.eq_of_jets_of_natDegree_lt θ D hθ _ H
    (reconstruct_natDegree_lt θ D hD a J) hH
    (fun i => (reconstruct_jets θ D a J ha i).trans (hJ i))

/-- Form the required scalar inverse directly from the supplied inverses of
the node differences. -/
def constantInverse (D : ℕ) (δinv : ι → ι → A) (i : ι) : A :=
  ∏ j ∈ Finset.univ.erase i, δinv i j ^ D

theorem constantInverse_correct (θ : ι → A) (D : ℕ) (δinv : ι → ι → A)
    (hδ : ∀ i j, i ≠ j → δinv i j * (θ i - θ j) = 1) (i : ι) :
    constantInverse D δinv i * (localFactor θ D i).coeff 0 = 1 := by
  simp only [constantInverse, localFactor, coeff_zero_eq_eval_zero, eval_comp,
    eval_add, eval_X, eval_C, zero_add, JetCRT.cofactor, eval_prod,
    JetCRT.nodePower, eval_pow, eval_sub]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j hj
  rw [← mul_pow, hδ i j (Finset.mem_erase.mp hj).1.symm, one_pow]

theorem denseGeometric_denote (z : List A) (D : ℕ) :
    PolynomialAlgorithm.denote (denseGeometricWithCost z D).1.1 =
        PolynomialAlgorithm.denote z ^ D ∧
      PolynomialAlgorithm.denote (denseGeometricWithCost z D).1.2 =
        ∑ j ∈ Finset.range D, PolynomialAlgorithm.denote z ^ j := by
  simp only [denseGeometricWithCost, geometricLoopWithCost_value]
  exact geometricLoop_denote [] [1]
    (fun x y => (PolynomialAlgorithm.addWithCost x y).1)
    (fun x y => (PolynomialAlgorithm.mulWithCost x y).1) z PolynomialAlgorithm.denote
    (by simp) (by simp) PolynomialAlgorithm.denote_addWithCost
    PolynomialAlgorithm.denote_mulWithCost D

theorem denseInverse_denote (B : List A) (a : A) (D : ℕ) :
    PolynomialAlgorithm.denote (denseInverseWithCost B a D).1 =
      inverse (PolynomialAlgorithm.denote B) a D := by
  simp only [denseInverseWithCost, PolynomialAlgorithm.denote_truncate,
    PolynomialAlgorithm.denote_scaleWithCost]
  rw [(denseGeometric_denote _ D).2]
  simp [inverse, rawInverse, sub_eq_add_neg]

theorem denseCorrection_denote (B J : List A) (a : A) (D : ℕ) :
    PolynomialAlgorithm.denote (denseCorrectionWithCost B J a D).1 =
      correctedJet (PolynomialAlgorithm.denote B) (PolynomialAlgorithm.denote J) a D := by
  simp [denseCorrectionWithCost, denseInverse_denote, correctedJet]

theorem denseGeometric_length (z : List A) (D : ℕ) :
    (denseGeometricWithCost z D).1.1.length ≤ 1 + D * z.length ∧
      (denseGeometricWithCost z D).1.2.length ≤ 1 + D * z.length := by
  simp only [denseGeometricWithCost, geometricLoopWithCost_value]
  exact geometricLoop_size_le [] [1]
    (fun x y => (PolynomialAlgorithm.addWithCost x y).1)
    (fun x y => (PolynomialAlgorithm.mulWithCost x y).1) z List.length
    (by simp) (by simp) (fun x y => (PolynomialAlgorithm.addWithCost_length x y).le)
    PolynomialAlgorithm.mulWithCost_length_le D

theorem denseGeometric_cost_le (z : List A) (D L : ℕ) (hz : z.length ≤ L) :
    (denseGeometricWithCost z D).2 ≤ D * (2 * (1 + D * L) * L + (1 + D * L)) := by
  apply geometricLoopWithCost_cost_le
  · intro k hk
    have hp := (denseGeometric_length z k).1
    have hp' : (denseGeometricWithCost z k).1.1.length ≤ 1 + D * L := by
      calc
        _ ≤ 1 + k * z.length := hp
        _ ≤ 1 + D * L := by gcongr
    dsimp only [denseGeometricWithCost] at hp'
    exact (PolynomialAlgorithm.mulWithCost_cost_le _ _).trans (by gcongr)
  · intro k hk
    have hs := (denseGeometric_length z k).2
    have hs' : (denseGeometricWithCost z k).1.2.length ≤ 1 + D * L := by
      calc
        _ ≤ 1 + k * z.length := hs
        _ ≤ 1 + D * L := by gcongr
    rw [PolynomialAlgorithm.addWithCost_cost]
    exact (Nat.min_le_left _ _).trans hs'

theorem denseInverse_length (B : List A) (a : A) (D : ℕ) :
    (denseInverseWithCost B a D).1.length ≤ D :=
  PolynomialAlgorithm.length_truncate_le D _

/-- A genuine coefficient-ring operation bound for the instrumented inverse.
`L` is any positive bound on the input coefficient-list length. -/
theorem denseInverse_cost_le (B : List A) (a : A) (D L : ℕ)
    (hL : 1 ≤ L) (hB : B.length ≤ L) :
    (denseInverseWithCost B a D).2 ≤
      L + 2 + D * (2 * (1 + D * L) * L + (1 + D * L)) + (1 + D * L) := by
  let z := (PolynomialAlgorithm.addWithCost [1]
    (PolynomialAlgorithm.scaleWithCost ((-1) * a) B).1).1
  have hz : z.length ≤ L := by
    simp only [z, PolynomialAlgorithm.addWithCost_length,
      PolynomialAlgorithm.scaleWithCost_length, List.length_singleton]
    exact max_le hL hB
  have hg := denseGeometric_cost_le z D L hz
  have hs : (denseGeometricWithCost z D).1.2.length ≤ 1 + D * L :=
    (denseGeometric_length z D).2.trans (by gcongr)
  change 1 + (PolynomialAlgorithm.scaleWithCost ((-1) * a) B).2 +
    (PolynomialAlgorithm.addWithCost [1]
      (PolynomialAlgorithm.scaleWithCost ((-1) * a) B).1).2 +
      (denseGeometricWithCost z D).2 +
      (PolynomialAlgorithm.scaleWithCost a (denseGeometricWithCost z D).1.2).2 ≤ _
  simp only [PolynomialAlgorithm.scaleWithCost_cost, PolynomialAlgorithm.addWithCost_cost,
    PolynomialAlgorithm.scaleWithCost_length, List.length_singleton]
  have hmin : min 1 B.length ≤ 1 := Nat.min_le_left _ _
  omega

theorem denseCorrection_length (B J : List A) (a : A) (D : ℕ) :
    (denseCorrectionWithCost B J a D).1.length ≤ D :=
  PolynomialAlgorithm.length_truncate_le D _

theorem denseCorrection_cost_le (B J : List A) (a : A) (D L : ℕ)
    (hL : 1 ≤ L) (hB : B.length ≤ L) (hJ : J.length ≤ D) :
    (denseCorrectionWithCost B J a D).2 ≤
      L + 2 + D * (2 * (1 + D * L) * L + (1 + D * L)) + (1 + D * L) + 2 * D * D := by
  have hi := denseInverse_cost_le B a D L hL hB
  have hp : (PolynomialAlgorithm.mulWithCost J (denseInverseWithCost B a D).1).2 ≤
      2 * D * D := by
    apply (PolynomialAlgorithm.mulWithCost_cost_le _ _).trans
    have hv := denseInverse_length B a D
    gcongr
  exact Nat.add_le_add hi hp

theorem denseFactors_denote {I : Type*} [DecidableEq I]
    (θ : I → A) (D : ℕ) (i : I) (js : List I) :
    ((denseFactorsWithCost θ D i js).1.map PolynomialAlgorithm.denote).prod =
      (js.map fun j => if j = i then 1 else JetCRT.nodePower (θ j) D).prod := by
  induction js with
  | nil => simp [denseFactorsWithCost]
  | cons j js ih =>
      have hlinear : PolynomialAlgorithm.denote [(-1) * θ j, 1] = X - C (θ j) := by
        simp [PolynomialAlgorithm.denote]
        ring
      by_cases h : j = i
      · simpa [denseFactorsWithCost, h] using ih
      · simp [denseFactorsWithCost, h, JetCRT.nodePower, ih,
          sub_eq_add_neg, add_comm]

theorem denseFactors_fin_denote {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (i : Fin Q) :
    ((denseFactorsWithCost θ D i (List.ofFn id)).1.map PolynomialAlgorithm.denote).prod =
      JetCRT.cofactor θ D i := by
  rw [denseFactors_denote]
  simp only [List.map_ofFn, Function.comp_def, id_eq, List.prod_ofFn]
  rw [← Finset.prod_erase (a := i) (f := fun j => if j = i then 1 else JetCRT.nodePower (θ j) D)
    Finset.univ (by simp)]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem denseCofactor_denote {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (i : Fin Q) :
    PolynomialAlgorithm.denote (denseCofactorWithCost θ D i).1 = JetCRT.cofactor θ D i := by
  simp only [denseCofactorWithCost, PolynomialAlgorithm.denote_productWithCost]
  exact denseFactors_fin_denote θ D i

theorem denseTerm_denote {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) (i : Fin Q) :
    PolynomialAlgorithm.denote (denseTermWithCost θ D a J i).1 =
      JetCRT.cofactor θ D i *
        (correction θ D a (fun j => PolynomialAlgorithm.denote (J j)) i).comp (X - C (θ i)) := by
  simp [denseTermWithCost, denseCofactor_denote, denseCorrection_denote,
    correction, localFactor, sub_eq_add_neg]

theorem denseCRT_denote {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) :
    PolynomialAlgorithm.denote (denseCRTWithCost θ D a J).1 =
      reconstruct θ D a (fun i => PolynomialAlgorithm.denote (J i)) := by
  simp [denseCRTWithCost, PolynomialAlgorithm.denote_sumWithCost, Function.comp_def, denseTerm_denote, reconstruct, List.sum_ofFn]

theorem denseCofactor_length {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (i : Fin Q) :
    (denseCofactorWithCost θ D i).1.length ≤ cofactorLength Q D := by
  have hn : (denseFactorsWithCost θ D i (List.ofFn id)).1.length ≤ Q * D := by
    simpa using denseFactors_length θ D i (List.ofFn id)
  have hp := PolynomialAlgorithm.productWithCost_length_le _ 2
    (denseFactors_each_length θ D i (List.ofFn id))
  apply hp.trans
  dsimp [cofactorLength]
  omega

theorem denseCofactor_cost_le {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (i : Fin Q) :
    (denseCofactorWithCost θ D i).2 ≤ cofactorCost Q D := by
  have hn : (denseFactorsWithCost θ D i (List.ofFn id)).1.length ≤ Q * D := by
    simpa using denseFactors_length θ D i (List.ofFn id)
  have hc : (denseFactorsWithCost θ D i (List.ofFn id)).2 ≤ Q := by
    simpa using denseFactors_cost θ D i (List.ofFn id)
  have hp := PolynomialAlgorithm.productWithCost_cost_le _ 2
    (denseFactors_each_length θ D i (List.ofFn id))
  change _ + _ ≤ _
  apply (Nat.add_le_add hc hp).trans
  dsimp [cofactorCost]
  calc
    _ = Q + 4 * (denseFactorsWithCost θ D i (List.ofFn id)).1.length *
        (1 + 2 * (denseFactorsWithCost θ D i (List.ofFn id)).1.length) := by ring
    _ ≤ _ := by gcongr

theorem denseTerm_length {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) (i : Fin Q) :
    (denseTermWithCost θ D a J i).1.length ≤ termLength Q D := by
  have hc := denseCofactor_length θ D i
  have hi := denseCorrection_length
    (PolynomialAlgorithm.shiftWithCost (θ i) (denseCofactorWithCost θ D i).1).1 (J i) (a i) D
  have hs := PolynomialAlgorithm.shiftWithCost_length_le ((-1) * θ i)
    (denseCorrectionWithCost
      (PolynomialAlgorithm.shiftWithCost (θ i) (denseCofactorWithCost θ D i).1).1 (J i) (a i) D).1
  have hm := PolynomialAlgorithm.mulWithCost_length_le (denseCofactorWithCost θ D i).1
    (PolynomialAlgorithm.shiftWithCost ((-1) * θ i)
      (denseCorrectionWithCost
        (PolynomialAlgorithm.shiftWithCost (θ i) (denseCofactorWithCost θ D i).1).1 (J i) (a i) D).1).1
  change _ ≤ cofactorLength Q D + 2 * D
  exact hm.trans (by omega)

theorem denseTerm_cost_le {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) (hJ : ∀ i, (J i).length ≤ D) (i : Fin Q) :
    (denseTermWithCost θ D a J i).2 ≤ termCost Q D := by
  let c := denseCofactorWithCost θ D i
  let s := PolynomialAlgorithm.shiftWithCost (θ i) c.1
  let r := denseCorrectionWithCost s.1 (J i) (a i) D
  let u := PolynomialAlgorithm.shiftWithCost ((-1) * θ i) r.1
  have hc : c.2 ≤ cofactorCost Q D := denseCofactor_cost_le θ D i
  have hcl : c.1.length ≤ cofactorLength Q D := denseCofactor_length θ D i
  have hsl : s.1.length ≤ 2 * cofactorLength Q D :=
    (PolynomialAlgorithm.shiftWithCost_length_le _ _).trans (by gcongr)
  have hs : s.2 ≤ 5 * cofactorLength Q D ^ 2 :=
    (PolynomialAlgorithm.shiftWithCost_cost_le _ _).trans (by gcongr)
  have hr : r.2 ≤ inverseCost D (2 * cofactorLength Q D) + 2 * D * D := by
    apply denseCorrection_cost_le _ _ _ _ _ _ hsl (hJ i)
    dsimp [cofactorLength]
    omega
  have hrl : r.1.length ≤ D := denseCorrection_length _ _ _ _
  have hul : u.1.length ≤ 2 * D :=
    (PolynomialAlgorithm.shiftWithCost_length_le _ _).trans (by gcongr)
  have hu : u.2 ≤ 5 * D ^ 2 :=
    (PolynomialAlgorithm.shiftWithCost_cost_le _ _).trans (by gcongr)
  have hm : (PolynomialAlgorithm.mulWithCost c.1 u.1).2 ≤ 4 * cofactorLength Q D * D := by
    apply (PolynomialAlgorithm.mulWithCost_cost_le _ _).trans
    calc
      _ ≤ 2 * cofactorLength Q D * (2 * D) := by gcongr
      _ = _ := by ring
  change c.2 + s.2 + r.2 + 1 + u.2 + (PolynomialAlgorithm.mulWithCost c.1 u.1).2 ≤ _
  dsimp only [termCost]
  omega

theorem denseCRT_cost_le {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) (hJ : ∀ i, (J i).length ≤ D) :
    (denseCRTWithCost θ D a J).2 ≤ crtCost Q D := by
  let terms := List.ofFn (fun i => denseTermWithCost θ D a J i)
  have hlength : ∀ P ∈ terms.map Prod.fst, P.length ≤ termLength Q D := by
    intro P hP
    simp only [terms, List.map_ofFn, Function.comp_def, List.mem_ofFn] at hP
    obtain ⟨i, rfl⟩ := hP
    exact denseTerm_length θ D a J i
  have hs := PolynomialAlgorithm.sumWithCost_cost_le (terms.map Prod.fst)
    (termLength Q D) hlength
  have ht : (terms.map Prod.snd).sum ≤ Q * termCost Q D := by
    simp only [terms, List.map_ofFn, Function.comp_def, List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin Q, termCost Q D := Finset.sum_le_sum (fun i _ => denseTerm_cost_le θ D a J hJ i)
      _ = _ := by simp
  simp only [List.length_map, terms, List.length_ofFn] at hs
  change _ + _ ≤ _
  apply (Nat.add_le_add ht hs).trans
  exact le_of_eq (by dsimp [crtCost]; ring)

/-- The complete executable dense-list algorithm recovers the polynomial.
The supplied scalar inverse certificates are the sole inverse-related input. -/
theorem denseCRT_correct {Q : ℕ} [NeZero Q] [Nontrivial A]
    (θ : Fin Q → A) (D : ℕ) (hD : 0 < D)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j))
    (a : Fin Q → A) (J : Fin Q → List A)
    (ha : ∀ i, a i * (localFactor θ D i).coeff 0 = 1)
    (H : A[X]) (hH : H.natDegree < Q * D)
    (hJ : ∀ i, Truncation.trunc D (PolynomialAlgorithm.denote (J i)) = JetCRT.jet (θ i) D H) :
    PolynomialAlgorithm.denote (denseCRTWithCost θ D a J).1 = H := by
  rw [denseCRT_denote]
  apply reconstruct_eq θ D hD hθ a _ ha H _ hJ
  simpa using hH

end SubexponentialSAT.TruncatedInverse

end
end OAI.Algorithms
