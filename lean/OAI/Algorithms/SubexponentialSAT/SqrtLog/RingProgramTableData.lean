import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableLoop

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Materialized coefficient vector together with its cached final coefficient. -/
structure VectorData (B d : ℕ) where
  coefficients : List.Vector (Word B) d
  last : Word B

def wordBits {B : ℕ} (xs : List (Word B)) : List Bool := (xs.map Subtype.val).flatten

@[simp] theorem wordBits_length {B : ℕ} (xs : List (Word B)) :
    (wordBits xs).length = xs.length * B := by
  induction xs with
  | nil => simp [wordBits]
  | cons x xs ih =>
      simp only [wordBits, List.map_cons, List.flatten_cons, List.length_append,
        List.length_cons]
      change x.val.length + (wordBits xs).length = (xs.length + 1) * B
      rw [x.property, ih]
      ring

def outputWords (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail minusOne : Word (baseWidth p t)) : Pairs (baseWidth p t) → Word (baseWidth p t) → List (Word (baseWidth p t))
  | [], _ => []
  | (c,a) :: pairs, previous =>
    coefficient p t M tail c minusOne previous :: outputWords p t M tail minusOne pairs a

@[simp] theorem outputWords_length (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t)) :
    (outputWords p t M tail minusOne pairs previous).length = pairs.length := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair pairs ih => simpa [outputWords] using congrArg Nat.succ (ih pair.2)

theorem outputWords_bits (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t)) :
    wordBits (outputWords p t M tail minusOne pairs previous) =
      outputBits p t M tail minusOne pairs previous := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair pairs ih => simp [wordBits, outputWords, outputBits, ← ih pair.2]

def lastOutputWord (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail minusOne : Word (baseWidth p t)) : Pairs (baseWidth p t) → Word (baseWidth p t) → Word (baseWidth p t) → Word (baseWidth p t)
  | [], _, old => old
  | (c,a) :: pairs, previous, _ =>
    lastOutputWord p t M tail minusOne pairs a (coefficient p t M tail c minusOne previous)

theorem lastProduced_word (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous old : Word (baseWidth p t)) :
    lastProduced p t M tail minusOne pairs previous old.val =
      (lastOutputWord p t M tail minusOne pairs previous old).val := by
  induction pairs generalizing previous old with
  | nil => rfl
  | cons pair pairs ih => exact ih pair.2 _

theorem lastProduced_independent (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t))
    (hn : pairs ≠ []) (x y : List Bool) :
    lastProduced p t M tail minusOne pairs previous x =
      lastProduced p t M tail minusOne pairs previous y := by
  cases pairs with
  | nil => exact False.elim (hn rfl)
  | cons pair pairs => rfl

def advance (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (zeroWord minusOne : Word (baseWidth p t)) {d : ℕ}
    (c : List.Vector (Word (baseWidth p t)) d) (v : VectorData (baseWidth p t) d) :
    VectorData (baseWidth p t) d :=
  let pairs := c.val.zip v.coefficients.val
  { coefficients := ⟨outputWords p t M v.last minusOne pairs zeroWord, by simp [pairs]⟩
    last := lastOutputWord p t M v.last minusOne pairs zeroWord zeroWord }

@[simp] theorem leftBits_zip {B d : ℕ} (x y : List.Vector (Word B) d) :
    RingScan.leftBits (x.val.zip y.val) = wordBits x.val := by
  have h (xs ys : List (Word B)) (hl : xs.length = ys.length) :
      RingScan.leftBits (xs.zip ys) = wordBits xs := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all [RingScan.leftBits, wordBits]
    | cons x xs ih =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        change x.val ++ RingScan.leftBits (xs.zip ys) = x.val ++ wordBits xs
        exact congrArg (x.val ++ ·) (ih ys (by simpa using hl))
  exact h _ _ (x.property.trans y.property.symm)

@[simp] theorem rightBits_zip {B d : ℕ} (x y : List.Vector (Word B) d) :
    RingScan.rightBits (x.val.zip y.val) = wordBits y.val := by
  have h (xs ys : List (Word B)) (hl : xs.length = ys.length) :
      RingScan.rightBits (xs.zip ys) = wordBits ys := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all [RingScan.rightBits, wordBits]
    | cons x xs ih =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        change y.val ++ RingScan.rightBits (xs.zip ys) = y.val ++ wordBits ys
        exact congrArg (y.val ++ ·) (ih ys (by simpa using hl))
  exact h _ _ (x.property.trans y.property.symm)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
