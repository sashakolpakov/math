import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorFrames
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorCode

namespace OAI.Algorithms

/-! The physical padded cache format agrees coefficient by coefficient with
the Taylor arrays consumed by the counting program. -/

namespace SubexponentialSAT.SubexpTaylorCacheSemantics

open SubexpTaylorControl SubexpTaylorFrames SubexpExponentProgram

def retain {C : Type*} (zero : C) : ℕ → List C → List C
  | 0, _ => []
  | n + 1, [] => zero :: retain zero n []
  | n + 1, a :: P => a :: retain zero n P

@[simp] theorem retain_length {C : Type*} (zero : C) (n : ℕ) (P : List C) :
    (retain zero n P).length = n := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => cases P <;> simp [retain, ih]

theorem retain_getD {C : Type*} (zero : C) (n : ℕ) (P : List C) (j : ℕ) (hj : j < n) :
    (retain zero n P).getD j zero = P.getD j zero := by
  induction n generalizing P j with
  | zero => omega
  | succ n ih =>
      cases P with
      | nil =>
          cases j with
          | zero => rfl
          | succ j => simpa [retain, List.getD_cons_succ] using ih [] j (by omega)
      | cons a P =>
          cases j with
          | zero => rfl
          | succ j => simpa [retain, List.getD_cons_succ] using ih P j (by omega)

theorem chunks_encode {C : Type*} (encode : C → List Bool) (zero : C) (B : ℕ)
    (hencode : ∀ a, (encode a).length = B)
    (hzero : encode zero = List.replicate B false) (n : ℕ) (P : List C) :
    chunks B n (encodeList encode P) = (retain zero n P).map encode := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
      cases P with
      | nil =>
          simpa [chunks, encodeList, retain, hzero] using
            (congrArg (fun xs => List.replicate B false :: xs) (ih []))
      | cons a P =>
          have ht : padTake B (encode a ++ encodeList encode P) = encode a := by
            rw [← hencode a]
            simp [padTake]
          have hd : (encode a ++ encodeList encode P).drop B = encodeList encode P := by
            rw [← hencode a]
            simp
          change padTake B (encode a ++ encodeList encode P) ::
            chunks B n ((encode a ++ encodeList encode P).drop B) =
              encode a :: (retain zero n P).map encode
          rw [ht, hd]
          exact congrArg (List.cons (encode a)) (ih P)

theorem decode_getD {C R : Type*} [CommSemiring R] (decode : C → R) (zero : C)
    (hzero : decode zero = 0) (P : List C) (j : ℕ) :
    decode (P.getD j zero) = (PolynomialAlgorithm.denote (P.map decode)).coeff j := by
  rw [PolynomialAlgorithm.coeff_denote]
  induction P generalizing j with
  | nil => simp [PolynomialAlgorithm.coeff, hzero]
  | cons a P ih =>
      cases j with
      | zero => rfl
      | succ j => exact ih j

theorem retain_decode_coeff {C R : Type*} [CommSemiring R] (decode : C → R) (zero : C)
    (hzero : decode zero = 0) (n : ℕ) (P : List C) (j : ℕ) (hj : j < n) :
    decode ((retain zero n P).getD j zero) =
      (PolynomialAlgorithm.denote (P.map decode)).coeff j := by
  rw [retain_getD zero n P j hj]
  exact decode_getD decode zero hzero P j

/-- After the full physical shift, the finite cache has the exact requested
Taylor coefficients, including zeros beyond the stored polynomial. -/
theorem shifted_cache_coeff {C R : Type*} [CommRing R]
    (decode : C → R) (zero : C) (hzero : decode zero = 0)
    (step : C → C → C) (theta : R)
    (hstep : ∀ a b, decode (step a b) = decode a * theta + decode b)
    (n : ℕ) (P : List C) (j : ℕ) (hj : j < n) :
    decode ((retain zero n (SubexpTaylorSemantics.compactShift step P)).getD j zero) =
      ((PolynomialAlgorithm.denote (P.map decode)).comp
        (Polynomial.X + Polynomial.C theta)).coeff j := by
  rw [retain_decode_coeff decode zero hzero n _ j hj,
    SubexpTaylorSemantics.compactShift_decode decode step theta hstep]

theorem shifted_cache_matches_callback {C R : Type*} [CommRing R]
    (ops : SubexpSymbolicCost.RepresentedRing C R) (zero : C)
    (hzero : ops.decode zero = 0) (step : C → C → C) (theta : C)
    (hstep : ∀ a b, ops.decode (step a b) = ops.decode a * ops.decode theta + ops.decode b)
    (n : ℕ) (P : List C) (j : ℕ) (hj : j < n) :
    ops.decode ((retain zero n (SubexpTaylorSemantics.compactShift step P)).getD j zero) =
      (PolynomialAlgorithm.denote
        ((SubexpDensePolynomial.shiftProgram ops.program theta P).1.map ops.decode)).coeff j := by
  rw [retain_decode_coeff ops.decode zero hzero n _ j hj]
  exact SubexpTaylorSemantics.compactShift_coeff_eq_shiftProgram ops step theta hstep P j

end SubexponentialSAT.SubexpTaylorCacheSemantics

end OAI.Algorithms
