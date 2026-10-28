import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.TruncatedInverse
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

namespace OAI.Algorithms

/-!
# Uniform polynomial and CRT costs with growing parameters

These bounds apply to the existing executable coefficient-list algorithms.
Their numerical constants and exponents are absolute: in particular, `Q`, `D`,
the path degree, the extension degree, and coefficient width are not fixed.
Scalar-operation counters and serialized bit lengths are distinguished from
the separate task of proving a Turing-machine simulation.
-/

namespace SubexponentialSAT.SubexpPolynomialCost

open Polynomial
open scoped BigOperators

/-- A fixed polynomial bounding the actual dense CRT scalar-operation counter. -/
def uniformCrtOps (Q D : ℕ) : ℕ := 128 * (Q + 1) ^ 3 * (D + 1) ^ 4

/-- A fixed polynomial bounding the actual local-inverse counter. -/
def uniformInverseOps (D L : ℕ) : ℕ := 16 * (D + 1) ^ 2 * (L + 1) ^ 2

theorem crtCost_le_uniform (Q D : ℕ) :
    TruncatedInverse.crtCost Q D ≤ uniformCrtOps Q D := by
  dsimp [TruncatedInverse.crtCost, TruncatedInverse.termCost,
    TruncatedInverse.termLength, TruncatedInverse.cofactorCost,
    TruncatedInverse.cofactorLength, TruncatedInverse.inverseCost, uniformCrtOps]
  ring_nf
  omega

theorem inverseCost_le_uniform (D L : ℕ) :
    TruncatedInverse.inverseCost D L ≤ uniformInverseOps D L := by
  dsimp [TruncatedInverse.inverseCost, uniformInverseOps]
  ring_nf
  omega

theorem outputSlots_le_uniform (Q D : ℕ) :
    TruncatedInverse.termLength Q D ≤ 4 * (Q + 1) * (D + 1) := by
  dsimp [TruncatedInverse.termLength, TruncatedInverse.cofactorLength]
  ring_nf
  omega

theorem geometricSlots_le_uniform (Q D : ℕ) :
    1 + D * (2 * TruncatedInverse.cofactorLength Q D) ≤
      8 * (Q + 1) * (D + 1) ^ 2 := by
  dsimp [TruncatedInverse.cofactorLength]
  ring_nf
  omega

/-- One size parameter containing every growing argument relevant here. -/
def parameterSize (Q D R h b : ℕ) : ℕ := Q + D + R + h + b + 2

theorem uniformCrtOps_le_parameterSize (Q D R h b : ℕ) :
    uniformCrtOps Q D ≤ 128 * parameterSize Q D R h b ^ 7 := by
  let S := parameterSize Q D R h b
  have hQ : Q + 1 ≤ S := by dsimp [S, parameterSize]; omega
  have hD : D + 1 ≤ S := by dsimp [S, parameterSize]; omega
  calc
    uniformCrtOps Q D ≤ 128 * S ^ 3 * S ^ 4 := by unfold uniformCrtOps; gcongr
    _ = 128 * S ^ 7 := by ring

theorem outputBits_le_parameterSize (Q D R h b : ℕ) :
    4 * h * b * (Q + 1) * (D + 1) ^ 2 ≤ 4 * parameterSize Q D R h b ^ 5 := by
  let S := parameterSize Q D R h b
  have hQ : Q + 1 ≤ S := by dsimp [S, parameterSize]; omega
  have hD : D + 1 ≤ S := by dsimp [S, parameterSize]; omega
  have hh : h ≤ S := by dsimp [S, parameterSize]; omega
  have hb : b ≤ S := by dsimp [S, parameterSize]; omega
  calc
    4 * h * b * (Q + 1) * (D + 1) ^ 2 ≤ 4 * S * S * S * S ^ 2 := by gcongr
    _ = 4 * S ^ 5 := by ring

section InversePreprocessing

variable {A : Type*} [CommRing A]

/-- A finite scalar power loop, with one counted multiplication per step. -/
def scalarPowerWithCost (a : A) : ℕ → A × ℕ
  | 0 => (1, 0)
  | n + 1 =>
      let previous := scalarPowerWithCost a n
      (previous.1 * a, previous.2 + 1)

@[simp] theorem scalarPower_value (a : A) (n : ℕ) :
    (scalarPowerWithCost a n).1 = a ^ n := by
  induction n with
  | zero => simp [scalarPowerWithCost]
  | succ n ih => simp [scalarPowerWithCost, ih, pow_succ]

@[simp] theorem scalarPower_cost (a : A) (n : ℕ) :
    (scalarPowerWithCost a n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scalarPowerWithCost, ih]

def scalarProductWithCost : List A → A × ℕ
  | [] => (1, 0)
  | a :: as =>
      let previous := scalarProductWithCost as
      (a * previous.1, previous.2 + 1)

@[simp] theorem scalarProduct_value (as : List A) :
    (scalarProductWithCost as).1 = as.prod := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [scalarProductWithCost, ih]

@[simp] theorem scalarProduct_cost (as : List A) :
    (scalarProductWithCost as).2 = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [scalarProductWithCost, ih]

/-- Compute one local constant inverse from supplied pairwise inverses. -/
def constantInverseWithCost {Q : ℕ} (δinv : Fin Q → Fin Q → A) (D : ℕ) (i : Fin Q) : A × ℕ :=
  let powers := List.ofFn (fun j => if j = i then (1, 0) else scalarPowerWithCost (δinv i j) D)
  let product := scalarProductWithCost (powers.map Prod.fst)
  (product.1, (powers.map Prod.snd).sum + product.2)

theorem constantInverse_value {Q : ℕ} (δinv : Fin Q → Fin Q → A) (D : ℕ) (i : Fin Q) :
    (constantInverseWithCost δinv D i).1 = TruncatedInverse.constantInverse D δinv i := by
  simp only [constantInverseWithCost, scalarProduct_value, List.map_ofFn, Function.comp_def]
  simp only [apply_ite Prod.fst, scalarPower_value, List.prod_ofFn]
  rw [← Finset.prod_erase (a := i) (f := fun j => if j = i then 1 else δinv i j ^ D)
    Finset.univ (by simp)]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem constantInverse_cost {Q : ℕ} (δinv : Fin Q → Fin Q → A) (D : ℕ) (i : Fin Q) :
    (constantInverseWithCost δinv D i).2 ≤ Q * (D + 1) := by
  simp only [constantInverseWithCost, scalarProduct_cost,
    List.length_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  have hs : (∑ j : Fin Q, (if j = i then (1, 0) else scalarPowerWithCost (δinv i j) D).2) ≤ Q * D := by
    calc
      _ ≤ ∑ _j : Fin Q, D := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : j = i <;> simp [h]
      _ = _ := by simp
  calc
    _ ≤ Q * D + Q := Nat.add_le_add_right hs Q
    _ = Q * (D + 1) := by ring

/-- Cache the computed constant inverses in a finite vector before running
the dense CRT. Indexing the vector performs no hidden scalar inversion. -/
def crtFromDifferences {Q : ℕ} (θ : Fin Q → A) (D : ℕ)
    (δinv : Fin Q → Fin Q → A) (J : Fin Q → List A) : List A × ℕ :=
  let table := List.Vector.ofFn (fun i => constantInverseWithCost δinv D i)
  let result := TruncatedInverse.denseCRTWithCost θ D (fun i => (table.get i).1) J
  (result.1, (table.toList.map Prod.snd).sum + result.2)

theorem crtFromDifferences_value {Q : ℕ} (θ : Fin Q → A) (D : ℕ)
    (δinv : Fin Q → Fin Q → A) (J : Fin Q → List A) :
    (crtFromDifferences θ D δinv J).1 =
      (TruncatedInverse.denseCRTWithCost θ D
        (TruncatedInverse.constantInverse D δinv) J).1 := by
  simp only [crtFromDifferences, List.Vector.get_ofFn, constantInverse_value]

end InversePreprocessing

section Operations

variable {A : Type*} [CommRing A]

/-- The existing executable loop has a uniform bound even when Q grows. -/
theorem denseCRT_cost_uniform {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) (hJ : ∀ i, (J i).length ≤ D) :
    (TruncatedInverse.denseCRTWithCost θ D a J).2 ≤ uniformCrtOps Q D :=
  (TruncatedInverse.denseCRT_cost_le θ D a J hJ).trans (crtCost_le_uniform Q D)

theorem crtFromDifferences_cost {Q : ℕ} (θ : Fin Q → A) (D : ℕ)
    (δinv : Fin Q → Fin Q → A) (J : Fin Q → List A) (hJ : ∀ i, (J i).length ≤ D) :
    (crtFromDifferences θ D δinv J).2 ≤ 129 * (Q + 1) ^ 3 * (D + 1) ^ 4 := by
  have hs : (∑ i : Fin Q, (constantInverseWithCost δinv D i).2) ≤ Q * (Q * (D + 1)) := by
    calc
      _ ≤ ∑ _i : Fin Q, Q * (D + 1) :=
        Finset.sum_le_sum (fun i _ => constantInverse_cost δinv D i)
      _ = _ := by simp
  simp only [crtFromDifferences, List.Vector.toList_ofFn, List.map_ofFn,
    Function.comp_def, List.sum_ofFn]
  apply (Nat.add_le_add hs (denseCRT_cost_uniform θ D _ J hJ)).trans
  dsimp [uniformCrtOps]
  ring_nf
  omega

theorem crtFromDifferences_cost_all_parameters {Q : ℕ} (θ : Fin Q → A)
    (D R h b : ℕ) (δinv : Fin Q → Fin Q → A) (J : Fin Q → List A)
    (hJ : ∀ i, (J i).length ≤ D) :
    (crtFromDifferences θ D δinv J).2 ≤ 129 * parameterSize Q D R h b ^ 7 := by
  apply (crtFromDifferences_cost θ D δinv J hJ).trans
  let S := parameterSize Q D R h b
  have hQ : Q + 1 ≤ S := by dsimp [S, parameterSize]; omega
  have hD : D + 1 ≤ S := by dsimp [S, parameterSize]; omega
  calc
    _ ≤ 129 * S ^ 3 * S ^ 4 := by gcongr
    _ = 129 * S ^ 7 := by ring

theorem denseCRT_length {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) :
    (TruncatedInverse.denseCRTWithCost θ D a J).1.length ≤
      TruncatedInverse.termLength Q D := by
  apply PolynomialAlgorithm.sumWithCost_length_le
  intro P hP
  simp only [List.map_ofFn, Function.comp_def, List.mem_ofFn] at hP
  obtain ⟨i, rfl⟩ := hP
  exact TruncatedInverse.denseTerm_length θ D a J i

theorem denseCRT_length_uniform {Q : ℕ} (θ : Fin Q → A) (D : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) :
    (TruncatedInverse.denseCRTWithCost θ D a J).1.length ≤
      4 * (Q + 1) * (D + 1) :=
  (denseCRT_length θ D a J).trans (outputSlots_le_uniform Q D)

theorem crtFromDifferences_length {Q : ℕ} (θ : Fin Q → A) (D : ℕ)
    (δinv : Fin Q → Fin Q → A) (J : Fin Q → List A) :
    (crtFromDifferences θ D δinv J).1.length ≤ 4 * (Q + 1) * (D + 1) := by
  rw [crtFromDifferences_value]
  exact denseCRT_length_uniform θ D _ J

theorem denseInverse_cost_uniform (B : List A) (a : A) (D L : ℕ)
    (hL : 1 ≤ L) (hB : B.length ≤ L) :
    (TruncatedInverse.denseInverseWithCost B a D).2 ≤ uniformInverseOps D L :=
  (TruncatedInverse.denseInverse_cost_le B a D L hL hB).trans (inverseCost_le_uniform D L)

/-- Bounds the two stored polynomial arrays in the geometric-inverse loop.
This is a per-array bound, not an unproved peak-memory claim for recursive code. -/
theorem inverse_working_buffers (B : List A) (a : A) (Q D : ℕ)
    (hB : B.length ≤ 2 * TruncatedInverse.cofactorLength Q D) :
    let z := (PolynomialAlgorithm.addWithCost [1]
      (PolynomialAlgorithm.scaleWithCost ((-1) * a) B).1).1
    (TruncatedInverse.denseGeometricWithCost z D).1.1.length ≤ 8 * (Q + 1) * (D + 1) ^ 2 ∧
      (TruncatedInverse.denseGeometricWithCost z D).1.2.length ≤ 8 * (Q + 1) * (D + 1) ^ 2 := by
  dsimp only
  let z := (PolynomialAlgorithm.addWithCost [1]
    (PolynomialAlgorithm.scaleWithCost ((-1) * a) B).1).1
  have hz : z.length ≤ 2 * TruncatedInverse.cofactorLength Q D := by
    simp only [z, PolynomialAlgorithm.addWithCost_length,
      PolynomialAlgorithm.scaleWithCost_length, List.length_singleton]
    apply max_le _ hB
    dsimp [TruncatedInverse.cofactorLength]
    omega
  have hb : 1 + D * z.length ≤ 8 * (Q + 1) * (D + 1) ^ 2 := by
    calc
      1 + D * z.length ≤ 1 + D * (2 * TruncatedInverse.cofactorLength Q D) := by gcongr
      _ ≤ _ := geometricSlots_le_uniform Q D
  exact ⟨(TruncatedInverse.denseGeometric_length z D).1.trans hb,
    (TruncatedInverse.denseGeometric_length z D).2.trans hb⟩

/-- An actual executable local inverse, its algebraic certificate, its output
length, and its uniform scalar-operation bound in one statement. -/
theorem localInverse_spec (B : List A) (a : A) (D L : ℕ)
    (hL : 1 ≤ L) (hB : B.length ≤ L)
    (ha : a * (PolynomialAlgorithm.denote B).coeff 0 = 1) :
    (X : A[X]) ^ D ∣ PolynomialAlgorithm.denote B *
        PolynomialAlgorithm.denote (TruncatedInverse.denseInverseWithCost B a D).1 - 1 ∧
      (TruncatedInverse.denseInverseWithCost B a D).1.length ≤ D ∧
      (TruncatedInverse.denseInverseWithCost B a D).2 ≤ uniformInverseOps D L := by
  refine ⟨?_, TruncatedInverse.denseInverse_length B a D,
    denseInverse_cost_uniform B a D L hL hB⟩
  rw [TruncatedInverse.denseInverse_denote]
  exact TruncatedInverse.inverse_correct _ a D ha

/-- The CRT algorithm is uniform in Q and D; inverse inputs are explicit and
the proof uses the genuine formal jets of H over a commutative ring. -/
theorem uniform_CRT_spec {Q : ℕ} [NeZero Q] [Nontrivial A]
    (θ : Fin Q → A) (D : ℕ) (hD : 0 < D)
    (hθ : Pairwise fun i j => IsUnit (θ i - θ j))
    (a : Fin Q → A) (J : Fin Q → List A)
    (ha : ∀ i, a i * (TruncatedInverse.localFactor θ D i).coeff 0 = 1)
    (H : A[X]) (hH : H.natDegree < Q * D)
    (hjets : ∀ i, Truncation.trunc D (PolynomialAlgorithm.denote (J i)) = JetCRT.jet (θ i) D H)
    (hlength : ∀ i, (J i).length ≤ D) :
    PolynomialAlgorithm.denote (TruncatedInverse.denseCRTWithCost θ D a J).1 = H ∧
      (TruncatedInverse.denseCRTWithCost θ D a J).1.length ≤ 4 * (Q + 1) * (D + 1) ∧
      (TruncatedInverse.denseCRTWithCost θ D a J).2 ≤ uniformCrtOps Q D :=
  ⟨TruncatedInverse.denseCRT_correct θ D hD hθ a J ha H hH hjets,
    denseCRT_length_uniform θ D a J, denseCRT_cost_uniform θ D a J hlength⟩

/-- Pairwise inverse certificates suffice for the executable reconstruction;
all cofactor constant inverses are computed by the counted preprocessing loop. -/
theorem crtFromDifferences_spec {Q : ℕ} [NeZero Q] [Nontrivial A]
    (θ : Fin Q → A) (D : ℕ) (hD : 0 < D)
    (δinv : Fin Q → Fin Q → A)
    (hδ : ∀ i j, i ≠ j → δinv i j * (θ i - θ j) = 1)
    (J : Fin Q → List A) (H : A[X]) (hH : H.natDegree < Q * D)
    (hjets : ∀ i, Truncation.trunc D (PolynomialAlgorithm.denote (J i)) = JetCRT.jet (θ i) D H)
    (hlength : ∀ i, (J i).length ≤ D) :
    PolynomialAlgorithm.denote (crtFromDifferences θ D δinv J).1 = H ∧
      (crtFromDifferences θ D δinv J).2 ≤ 129 * (Q + 1) ^ 3 * (D + 1) ^ 4 := by
  constructor
  · rw [crtFromDifferences_value]
    apply TruncatedInverse.denseCRT_correct θ D hD _ _ J _ H hH hjets
    · intro i j hij
      exact IsUnit.of_mul_eq_one_right _ (hδ i j hij)
    · exact TruncatedInverse.constantInverse_correct θ D δinv hδ
  · exact crtFromDifferences_cost θ D δinv J hlength

/-- A path degree bound is charged as a growing numerical parameter. -/
theorem pathEval_cost (P : List A) (x : A) (R : ℕ) (hP : P.length ≤ R + 1) :
    (PolynomialAlgorithm.evalWithCost x P).2 ≤ 2 * (R + 1) := by
  rw [PolynomialAlgorithm.evalWithCost_cost]
  exact Nat.mul_le_mul_left 2 hP

theorem pathShift_cost (P : List A) (x : A) (R : ℕ) (hP : P.length ≤ R + 1) :
    (PolynomialAlgorithm.shiftWithCost x P).2 ≤ 5 * (R + 1) ^ 2 :=
  (PolynomialAlgorithm.shiftWithCost_cost_le x P).trans (by gcongr)

theorem pathEval_spec (P : List A) (x : A) (R : ℕ) (hP : P.length ≤ R + 1) :
    (PolynomialAlgorithm.evalWithCost x P).1 = (PolynomialAlgorithm.denote P).eval x ∧
      (PolynomialAlgorithm.evalWithCost x P).2 ≤ 2 * (R + 1) :=
  ⟨PolynomialAlgorithm.evalWithCost_value x P, pathEval_cost P x R hP⟩

end Operations

section Encoding

variable {A : Type*}

/-- Concatenate fixed-width coefficient encodings. The width and coefficient
count are external format data; no constant-time access is assumed. -/
def packCoefficients (encode : A → List Bool) (P : List A) : List Bool :=
  P.flatMap encode

theorem packCoefficients_length_le (encode : A → List Bool) (w : ℕ)
    (hencode : ∀ a, (encode a).length ≤ w) (P : List A) :
    (packCoefficients encode P).length ≤ P.length * w := by
  induction P with
  | nil => simp [packCoefficients]
  | cons a P ih =>
      simp only [packCoefficients, List.flatMap_cons, List.length_append, List.length_cons] at *
      calc
        _ ≤ w + P.length * w := Nat.add_le_add (hencode a) ih
        _ = (P.length + 1) * w := by ring

/-- Encoding Q order-D jets requires at most Q*D coefficient slots. -/
theorem inputJets_bits {Q : ℕ} (J : Fin Q → List A) (D w : ℕ)
    (hJ : ∀ i, (J i).length ≤ D) (encode : A → List Bool)
    (hencode : ∀ a, (encode a).length ≤ w) :
    ((List.ofFn (fun i => packCoefficients encode (J i))).flatten).length ≤ Q * D * w := by
  rw [List.length_flatten]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin Q, D * w := by
      apply Finset.sum_le_sum
      intro i _
      exact (packCoefficients_length_le encode w hencode (J i)).trans
        (Nat.mul_le_mul_right w (hJ i))
    _ = Q * D * w := by simp [Nat.mul_assoc]

variable [CommRing A]

/-- A storage bound using an actual coefficient encoder of width h*(D+1)*b.
The logarithmic prime-width parameter b and extension degree h remain visible. -/
theorem CRT_output_bits {Q : ℕ} (θ : Fin Q → A) (D h b : ℕ) (a : Fin Q → A)
    (J : Fin Q → List A) (encode : A → List Bool)
    (hencode : ∀ x, (encode x).length ≤ h * (D + 1) * b) :
    (packCoefficients encode (TruncatedInverse.denseCRTWithCost θ D a J).1).length ≤
      4 * h * b * (Q + 1) * (D + 1) ^ 2 := by
  apply (packCoefficients_length_le encode _ hencode _).trans
  calc
    _ ≤ (4 * (Q + 1) * (D + 1)) * (h * (D + 1) * b) :=
      Nat.mul_le_mul_right _ (denseCRT_length_uniform θ D a J)
    _ = _ := by ring

/-- A fixed degree-five storage bound displaying every varying parameter. -/
theorem CRT_output_bits_all_parameters {Q : ℕ} (θ : Fin Q → A)
    (D R h b : ℕ) (a : Fin Q → A) (J : Fin Q → List A) (encode : A → List Bool)
    (hencode : ∀ x, (encode x).length ≤ h * (D + 1) * b) :
    (packCoefficients encode (TruncatedInverse.denseCRTWithCost θ D a J).1).length ≤
      4 * parameterSize Q D R h b ^ 5 :=
  (CRT_output_bits θ D h b a J encode hencode).trans (outputBits_le_parameterSize Q D R h b)

theorem crtFromDifferences_output_bits {Q : ℕ} (θ : Fin Q → A) (D h b : ℕ)
    (δinv : Fin Q → Fin Q → A) (J : Fin Q → List A) (encode : A → List Bool)
    (hencode : ∀ x, (encode x).length ≤ h * (D + 1) * b) :
    (packCoefficients encode (crtFromDifferences θ D δinv J).1).length ≤
      4 * h * b * (Q + 1) * (D + 1) ^ 2 := by
  rw [crtFromDifferences_value]
  exact CRT_output_bits θ D h b _ J encode hencode

end Encoding

section ActualRingEncoding

variable (p Q D h : ℕ) [Fact p.Prime]

/-- The concrete prime-power quotient encoder discharges the width premise.
This is a bit-length statement; it makes no claim about encoder runtime. -/
theorem liftRing_CRT_output_bits (hh : h ≠ 0)
    (θ : Fin Q → ActualLiftRing.Ring p h (D + 1))
    (δinv : Fin Q → Fin Q → ActualLiftRing.Ring p h (D + 1))
    (J : Fin Q → List (ActualLiftRing.Ring p h (D + 1))) :
    (packCoefficients (SubexpLiftRing.encodeLambda p h (D + 1) (Nat.zero_lt_succ D))
      (crtFromDifferences θ D δinv J).1).length ≤
        4 * h * (Nat.log 2 p + 1) * (Q + 1) * (D + 1) ^ 2 := by
  apply crtFromDifferences_output_bits
  intro x
  rw [SubexpLiftRing.encodeLambda_length p h (D + 1) (Nat.zero_lt_succ D) hh x]
  exact le_of_eq (Nat.mul_assoc _ _ _).symm

theorem quartic_CRT_output_bits
    (θ : Fin Q → ActualLiftRing.Ring p 4 (D + 1))
    (δinv : Fin Q → Fin Q → ActualLiftRing.Ring p 4 (D + 1))
    (J : Fin Q → List (ActualLiftRing.Ring p 4 (D + 1))) :
    (packCoefficients (SubexpLiftRing.encodeLambda p 4 (D + 1) (Nat.zero_lt_succ D))
      (crtFromDifferences θ D δinv J).1).length ≤
        16 * (Nat.log 2 p + 1) * (Q + 1) * (D + 1) ^ 2 := by
  simpa using liftRing_CRT_output_bits p Q D 4 (by decide) θ δinv J

theorem liftRing_inputJets_bits (hh : h ≠ 0)
    (J : Fin Q → List (ActualLiftRing.Ring p h (D + 1)))
    (hJ : ∀ i, (J i).length ≤ D) :
    ((List.ofFn (fun i => packCoefficients
      (SubexpLiftRing.encodeLambda p h (D + 1) (Nat.zero_lt_succ D)) (J i))).flatten).length ≤
        Q * D * (h * (D + 1) * (Nat.log 2 p + 1)) := by
  apply inputJets_bits J D _ hJ
  intro x
  rw [SubexpLiftRing.encodeLambda_length p h (D + 1) (Nat.zero_lt_succ D) hh x]
  exact le_of_eq (Nat.mul_assoc _ _ _).symm

end ActualRingEncoding

end SubexponentialSAT.SubexpPolynomialCost

end OAI.Algorithms
