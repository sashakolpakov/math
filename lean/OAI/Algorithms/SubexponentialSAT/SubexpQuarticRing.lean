import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
import OAI.Algorithms.SubexponentialSAT.QuarticSearch
import OAI.Algorithms.SubexponentialSAT.SubexpBaseNegation

namespace OAI.Algorithms

/-!
# A fixed-size, executable quartic ring implementation

The data are four coefficients.  Multiplication is Horner evaluation with
the explicit reduction `T^4 = t0 + t1*T + t2*T^2 + t3*T^3`.
The coefficient operations are parameters of the implementation; the binary
instance below discharges their correctness and uniform finite-event bound.
-/

namespace SubexponentialSAT.SubexpQuarticRing

structure Quad (A : Type*) where
  c0 : A
  c1 : A
  c2 : A
  c3 : A
  deriving DecidableEq

namespace Quad

def map {A B : Type*} (f : A → B) (a : Quad A) : Quad B :=
  ⟨f a.c0, f a.c1, f a.c2, f a.c3⟩

def ofFn {A : Type*} (f : Fin 4 → A) : Quad A := ⟨f 0, f 1, f 2, f 3⟩

def toFn {A : Type*} (a : Quad A) : Fin 4 → A := ![a.c0, a.c1, a.c2, a.c3]

@[simp] theorem map_map {A B C : Type*} (g : B → C) (f : A → B) (a : Quad A) :
    (a.map f).map g = a.map (g ∘ f) := rfl

end Quad

section RingFormulas

variable {R : Type*} [CommRing R]

def add (a b : Quad R) : Quad R :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

def scale (a : R) (b : Quad R) : Quad R :=
  ⟨a*b.c0, a*b.c1, a*b.c2, a*b.c3⟩

/-- One multiplication by the root, followed by the fixed quartic reduction. -/
def shift (t a : Quad R) : Quad R :=
  ⟨a.c3*t.c0, a.c0 + a.c3*t.c1, a.c1 + a.c3*t.c2, a.c2 + a.c3*t.c3⟩

def mul (t a b : Quad R) : Quad R :=
  add (scale a.c0 b) (shift t
    (add (scale a.c1 b) (shift t
      (add (scale a.c2 b) (shift t (scale a.c3 b))))))

variable {S : Type*} [CommRing S]

def denote (φ : R →+* S) (θ : S) (a : Quad R) : S :=
  φ a.c0 + φ a.c1 * θ + φ a.c2 * θ^2 + φ a.c3 * θ^3

theorem denote_add (φ : R →+* S) (θ : S) (a b : Quad R) :
    denote φ θ (add a b) = denote φ θ a + denote φ θ b := by
  simp only [denote, add, map_add]
  ring

theorem denote_scale (φ : R →+* S) (θ : S) (a : R) (b : Quad R) :
    denote φ θ (scale a b) = φ a * denote φ θ b := by
  simp only [denote, scale, map_mul]
  ring

theorem denote_shift (φ : R →+* S) (θ : S) (t a : Quad R)
    (hθ : θ^4 = denote φ θ t) :
    denote φ θ (shift t a) = θ * denote φ θ a := by
  have h : φ a.c3 * θ^4 = φ a.c3 * denote φ θ t := congrArg (φ a.c3 * ·) hθ
  simp only [denote, shift, map_add, map_mul] at *
  linear_combination -h

theorem denote_mul (φ : R →+* S) (θ : S) (t a b : Quad R)
    (hθ : θ^4 = denote φ θ t) :
    denote φ θ (mul t a b) = denote φ θ a * denote φ θ b := by
  simp only [mul, denote_add, denote_shift φ θ t _ hθ, denote_scale]
  unfold denote
  ring

end RingFormulas

/-! These loops execute exactly the displayed scalar calls. -/

section Executable

variable {A : Type*}

def addRun (addOp : A → A → A × ℕ) (a b : Quad A) : Quad A × ℕ :=
  let r0 := addOp a.c0 b.c0
  let r1 := addOp a.c1 b.c1
  let r2 := addOp a.c2 b.c2
  let r3 := addOp a.c3 b.c3
  (⟨r0.1, r1.1, r2.1, r3.1⟩, r0.2 + r1.2 + r2.2 + r3.2)

def scaleRun (mulOp : A → A → A × ℕ) (a : A) (b : Quad A) : Quad A × ℕ :=
  let r0 := mulOp a b.c0
  let r1 := mulOp a b.c1
  let r2 := mulOp a b.c2
  let r3 := mulOp a b.c3
  (⟨r0.1, r1.1, r2.1, r3.1⟩, r0.2 + r1.2 + r2.2 + r3.2)

def shiftRun (addOp mulOp : A → A → A × ℕ) (t a : Quad A) : Quad A × ℕ :=
  let r0 := mulOp a.c3 t.c0
  let r1 := mulOp a.c3 t.c1
  let r2 := mulOp a.c3 t.c2
  let r3 := mulOp a.c3 t.c3
  let s1 := addOp a.c0 r1.1
  let s2 := addOp a.c1 r2.1
  let s3 := addOp a.c2 r3.1
  (⟨r0.1, s1.1, s2.1, s3.1⟩,
    r0.2 + r1.2 + r2.2 + r3.2 + s1.2 + s2.2 + s3.2)

def mulRun (addOp mulOp : A → A → A × ℕ) (t a b : Quad A) : Quad A × ℕ :=
  let b3 := scaleRun mulOp a.c3 b
  let s3 := shiftRun addOp mulOp t b3.1
  let b2 := scaleRun mulOp a.c2 b
  let a2 := addRun addOp b2.1 s3.1
  let s2 := shiftRun addOp mulOp t a2.1
  let b1 := scaleRun mulOp a.c1 b
  let a1 := addRun addOp b1.1 s2.1
  let s1 := shiftRun addOp mulOp t a1.1
  let b0 := scaleRun mulOp a.c0 b
  let a0 := addRun addOp b0.1 s1.1
  (a0.1, b3.2 + s3.2 + b2.2 + a2.2 + s2.2 + b1.2 + a1.2 + s1.2 + b0.2 + a0.2)

variable {R : Type*} [CommRing R] (value : A → R)
  (addOp mulOp : A → A → A × ℕ)
  (hadd : ∀ a b, value (addOp a b).1 = value a + value b)
  (hmul : ∀ a b, value (mulOp a b).1 = value a * value b)

include hadd in
theorem addRun_correct (a b : Quad A) :
    ((addRun addOp a b).1).map value = add (a.map value) (b.map value) := by
  simp [addRun, Quad.map, add, hadd]

include hmul in
theorem scaleRun_correct (a : A) (b : Quad A) :
    ((scaleRun mulOp a b).1).map value = scale (value a) (b.map value) := by
  simp [scaleRun, Quad.map, scale, hmul]

include hadd hmul in
theorem shiftRun_correct (t a : Quad A) :
    ((shiftRun addOp mulOp t a).1).map value = shift (t.map value) (a.map value) := by
  simp [shiftRun, Quad.map, shift, hadd, hmul]

include hadd hmul in
theorem mulRun_correct (t a b : Quad A) :
    ((mulRun addOp mulOp t a b).1).map value = mul (t.map value) (a.map value) (b.map value) := by
  simp only [mulRun]
  simp only [addRun_correct value addOp hadd, shiftRun_correct value addOp mulOp hadd hmul,
    scaleRun_correct value mulOp hmul, mul]
  rfl

variable (C : ℕ) (ha : ∀ a b, (addOp a b).2 ≤ C) (hm : ∀ a b, (mulOp a b).2 ≤ C)

include ha in
theorem addRun_cost (a b : Quad A) : (addRun addOp a b).2 ≤ 4*C := by
  have h0 := ha a.c0 b.c0
  have h1 := ha a.c1 b.c1
  have h2 := ha a.c2 b.c2
  have h3 := ha a.c3 b.c3
  dsimp [addRun]
  omega

include hm in
theorem scaleRun_cost (a : A) (b : Quad A) : (scaleRun mulOp a b).2 ≤ 4*C := by
  have h0 := hm a b.c0
  have h1 := hm a b.c1
  have h2 := hm a b.c2
  have h3 := hm a b.c3
  dsimp [scaleRun]
  omega

include ha hm in
theorem shiftRun_cost (t a : Quad A) : (shiftRun addOp mulOp t a).2 ≤ 7*C := by
  have h0 := hm a.c3 t.c0
  have h1 := hm a.c3 t.c1
  have h2 := hm a.c3 t.c2
  have h3 := hm a.c3 t.c3
  have h4 := ha a.c0 (mulOp a.c3 t.c1).1
  have h5 := ha a.c1 (mulOp a.c3 t.c2).1
  have h6 := ha a.c2 (mulOp a.c3 t.c3).1
  dsimp [shiftRun]
  omega

include ha hm in
theorem mulRun_cost (t a b : Quad A) : (mulRun addOp mulOp t a b).2 ≤ 49*C := by
  have hb3 := scaleRun_cost mulOp C hm a.c3 b
  have hs3 := shiftRun_cost addOp mulOp C ha hm t (scaleRun mulOp a.c3 b).1
  have hb2 := scaleRun_cost mulOp C hm a.c2 b
  have ha2 := addRun_cost addOp C ha (scaleRun mulOp a.c2 b).1
    (shiftRun addOp mulOp t (scaleRun mulOp a.c3 b).1).1
  have hs2 := shiftRun_cost addOp mulOp C ha hm t
    (addRun addOp (scaleRun mulOp a.c2 b).1
      (shiftRun addOp mulOp t (scaleRun mulOp a.c3 b).1).1).1
  have hb1 := scaleRun_cost mulOp C hm a.c1 b
  have ha1 := addRun_cost addOp C ha (scaleRun mulOp a.c1 b).1
    (shiftRun addOp mulOp t
      (addRun addOp (scaleRun mulOp a.c2 b).1
        (shiftRun addOp mulOp t (scaleRun mulOp a.c3 b).1).1).1).1
  have hs1 := shiftRun_cost addOp mulOp C ha hm t
    (addRun addOp (scaleRun mulOp a.c1 b).1
      (shiftRun addOp mulOp t
        (addRun addOp (scaleRun mulOp a.c2 b).1
          (shiftRun addOp mulOp t (scaleRun mulOp a.c3 b).1).1).1).1).1
  have hb0 := scaleRun_cost mulOp C hm a.c0 b
  have ha0 := addRun_cost addOp C ha (scaleRun mulOp a.c0 b).1
    (shiftRun addOp mulOp t
      (addRun addOp (scaleRun mulOp a.c1 b).1
        (shiftRun addOp mulOp t
          (addRun addOp (scaleRun mulOp a.c2 b).1
            (shiftRun addOp mulOp t (scaleRun mulOp a.c3 b).1).1).1).1).1).1
  dsimp only [mulRun]
  omega

end Executable

section BinaryInstance

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing

/-- The type stores the width invariant; its alphabet remains `Bool`. -/
abbrev Word (B : ℕ) := { xs : List Bool // xs.length = B }

variable (p μ : ℕ) [Fact p.Prime]

def modulusBits : List Bool := fixedBits (baseWidth p μ + 1) (p^μ)

omit [Fact (Nat.Prime p)] in
@[simp] theorem modulusBits_length : (modulusBits p μ).length = baseWidth p μ + 1 :=
  fixedBits_length _ _

omit [Fact (Nat.Prime p)] in
@[simp] theorem modulusBits_value : BinaryArithmetic.toNat (modulusBits p μ) = p^μ := by
  apply toNat_fixedBits_of_lt
  exact (modulus_le_width p μ).trans_lt (by
    rw [pow_succ]
    have := Nat.two_pow_pos (baseWidth p μ)
    omega)

def wordValue (x : Word (baseWidth p μ)) : ZMod (p^μ) := (BinaryArithmetic.toNat x.val : ℕ)

def encodeWord (x : ZMod (p^μ)) : Word (baseWidth p μ) :=
  ⟨encodeBase p μ x, encodeBase_length p μ x⟩

@[simp] theorem wordValue_encodeWord (x : ZMod (p^μ)) :
    wordValue p μ (encodeWord p μ x) = x := by
  simp [wordValue, encodeWord, encodeBase_value]

def wordAdd (x y : Word (baseWidth p μ)) : Word (baseWidth p μ) × ℕ :=
  let r := addBaseRun (baseWidth p μ) (modulusBits p μ) x.val y.val
  (⟨r.1, addBaseRun_length _ _ _ _⟩, r.2)

def wordMul (x y : Word (baseWidth p μ)) : Word (baseWidth p μ) × ℕ :=
  let r := mulBaseRun (baseWidth p μ) (modulusBits p μ) x.val y.val
  (⟨r.1, mulBaseRun_length _ _ _ _⟩, r.2)

theorem wordAdd_correct (x y : Word (baseWidth p μ)) :
    wordValue p μ (wordAdd p μ x y).1 = wordValue p μ x + wordValue p μ y := by
  unfold wordValue wordAdd
  dsimp only
  rw [addBaseRun_value]
  · simp only [modulusBits_value, ZMod.natCast_mod, Nat.cast_add]
  · simpa only [modulusBits_value] using pow_pos (Fact.out : p.Prime).pos μ
  · simpa only [modulusBits_value] using modulus_le_width p μ

theorem wordMul_correct (x y : Word (baseWidth p μ)) :
    wordValue p μ (wordMul p μ x y).1 = wordValue p μ x * wordValue p μ y := by
  unfold wordValue wordMul
  dsimp only
  rw [mulBaseRun_value]
  · simp only [modulusBits_value, ZMod.natCast_mod, Nat.cast_mul]
  · simpa only [modulusBits_value] using pow_pos (Fact.out : p.Prime).pos μ
  · simpa only [modulusBits_value] using modulus_le_width p μ

def scalarBudget : ℕ := 200 * (baseWidth p μ + 2)^2 + 3 * baseWidth p μ

omit [Fact (Nat.Prime p)] in
theorem wordAdd_cost (x y : Word (baseWidth p μ)) :
    (wordAdd p μ x y).2 ≤ scalarBudget p μ := by
  have h := addBaseRun_cost (baseWidth p μ) (modulusBits p μ) x.val y.val
    (by simp) (by rw [x.property]) (by rw [y.property])
  change (addBaseRun _ _ _ _).2 ≤ _
  exact h.trans (by unfold scalarBudget; omega)

omit [Fact (Nat.Prime p)] in
theorem wordMul_cost (x y : Word (baseWidth p μ)) :
    (wordMul p μ x y).2 ≤ scalarBudget p μ :=
  mulBaseRun_cost (baseWidth p μ) (modulusBits p μ) x.val y.val
    (by simp) (by rw [x.property]) (by rw [y.property])

theorem wordAdd_canonical (x y : Word (baseWidth p μ)) :
    BinaryArithmetic.toNat (wordAdd p μ x y).1.val < p^μ := by
  change BinaryArithmetic.toNat (addBaseRun _ _ _ _).1 < _
  rw [addBaseRun_value _ _ _ _ (by
    simpa using pow_pos (Fact.out : p.Prime).pos μ) (by
    simpa using modulus_le_width p μ), modulusBits_value]
  exact Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos μ)

/-- Canonicalize once, then execute the verified bitwise modular negation.
This operation accepts every width-correct input, including unreduced words. -/
def wordNeg (x : Word (baseWidth p μ)) : Word (baseWidth p μ) × ℕ :=
  let reduced := wordAdd p μ x (encodeWord p μ 0)
  let r := SubexpBaseNegation.negBaseRun (baseWidth p μ) (modulusBits p μ) reduced.1.val
  (⟨r.1, SubexpBaseNegation.negBaseRun_length _ _ _⟩, reduced.2 + r.2)

theorem wordNeg_correct (x : Word (baseWidth p μ)) :
    wordValue p μ (wordNeg p μ x).1 = -wordValue p μ x := by
  have h := SubexpBaseNegation.negBaseRun_cast (baseWidth p μ) (modulusBits p μ)
    (wordAdd p μ x (encodeWord p μ 0)).1.val (by simp)
    (by rw [(wordAdd p μ x (encodeWord p μ 0)).1.property])
    (by simpa using pow_pos (Fact.out : p.Prime).pos μ)
    (by simpa using modulus_le_width p μ)
    (by simpa using wordAdd_canonical p μ x (encodeWord p μ 0))
  rw [modulusBits_value] at h
  change wordValue p μ (wordNeg p μ x).1 =
    -wordValue p μ (wordAdd p μ x (encodeWord p μ 0)).1 at h
  simpa only [wordAdd_correct, wordValue_encodeWord, add_zero] using h

omit [Fact (Nat.Prime p)] in
theorem wordNeg_cost (x : Word (baseWidth p μ)) :
    (wordNeg p μ x).2 ≤ scalarBudget p μ := by
  have ha := addBaseRun_cost (baseWidth p μ) (modulusBits p μ) x.val
    (encodeWord p μ 0).val (by simp) (by rw [x.property])
    (by rw [(encodeWord p μ 0).property])
  have hn := SubexpBaseNegation.negBaseRun_cost (baseWidth p μ) (modulusBits p μ)
    (wordAdd p μ x (encodeWord p μ 0)).1.val (by simp)
  change (wordAdd p μ x (encodeWord p μ 0)).2 +
    (SubexpBaseNegation.negBaseRun _ _ _).2 ≤ _
  change (wordAdd p μ x (encodeWord p μ 0)).2 ≤ _ at ha
  unfold scalarBudget
  omega

def binaryAdd (a b : Quad (Word (baseWidth p μ))) :
    Quad (Word (baseWidth p μ)) × ℕ := addRun (wordAdd p μ) a b

theorem binaryAdd_correct (a b : Quad (Word (baseWidth p μ))) :
    ((binaryAdd p μ a b).1).map (wordValue p μ) =
      add (a.map (wordValue p μ)) (b.map (wordValue p μ)) :=
  addRun_correct (wordValue p μ) (wordAdd p μ) (wordAdd_correct p μ) a b

omit [Fact (Nat.Prime p)] in
theorem binaryAdd_cost (a b : Quad (Word (baseWidth p μ))) :
    (binaryAdd p μ a b).2 ≤ 4 * scalarBudget p μ :=
  addRun_cost (wordAdd p μ) (scalarBudget p μ) (wordAdd_cost p μ) a b

def binaryNeg (a : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) × ℕ :=
  let r0 := wordNeg p μ a.c0
  let r1 := wordNeg p μ a.c1
  let r2 := wordNeg p μ a.c2
  let r3 := wordNeg p μ a.c3
  (⟨r0.1, r1.1, r2.1, r3.1⟩, r0.2 + r1.2 + r2.2 + r3.2)

theorem binaryNeg_correct (a : Quad (Word (baseWidth p μ))) :
    ((binaryNeg p μ a).1).map (wordValue p μ) = (a.map (wordValue p μ)).map Neg.neg := by
  simp [binaryNeg, Quad.map, wordNeg_correct]

omit [Fact (Nat.Prime p)] in
theorem binaryNeg_cost (a : Quad (Word (baseWidth p μ))) :
    (binaryNeg p μ a).2 ≤ 4 * scalarBudget p μ := by
  have h0 := wordNeg_cost p μ a.c0
  have h1 := wordNeg_cost p μ a.c1
  have h2 := wordNeg_cost p μ a.c2
  have h3 := wordNeg_cost p μ a.c3
  dsimp [binaryNeg]
  omega

/-- Actual binary quartic multiplication. Every output word has the same
width as the input words, including all intermediate coefficient words. -/
def binaryMul (t a b : Quad (Word (baseWidth p μ))) :
    Quad (Word (baseWidth p μ)) × ℕ := mulRun (wordAdd p μ) (wordMul p μ) t a b

theorem binaryMul_correct (t a b : Quad (Word (baseWidth p μ))) :
    ((binaryMul p μ t a b).1).map (wordValue p μ) =
      mul (t.map (wordValue p μ)) (a.map (wordValue p μ)) (b.map (wordValue p μ)) :=
  mulRun_correct (wordValue p μ) (wordAdd p μ) (wordMul p μ)
    (wordAdd_correct p μ) (wordMul_correct p μ) t a b

omit [Fact (Nat.Prime p)] in
/-- Forty-nine calls to concrete quadratic-cost binary scalar programs.
This is a source-event budget, not a machine simulation theorem. -/
theorem binaryMul_cost (t a b : Quad (Word (baseWidth p μ))) :
    (binaryMul p μ t a b).2 ≤
      49 * (200 * (μ * (Nat.log 2 p + 1) + 2)^2 + 3 * (μ * (Nat.log 2 p + 1))) :=
  mulRun_cost (wordAdd p μ) (wordMul p μ) (scalarBudget p μ)
    (wordAdd_cost p μ) (wordMul_cost p μ) t a b

end BinaryInstance

section QuotientRefinement

open Polynomial

variable {R : Type*} [CommRing R]

/-- The four reduction coefficients are the negatives of the four stored
coefficients of the monic defining polynomial. -/
def reductionData (c : Fin 4 → R) : Quad R := Quad.ofFn fun i => -c i

noncomputable def quotientDenote (c : Fin 4 → R) (a : Quad R) :
    LiftRing.Extension (QuarticSearch.poly c) :=
  denote (LiftRing.of (QuarticSearch.poly c))
    (LiftRing.mk (QuarticSearch.poly c) X) a

theorem quotient_root (c : Fin 4 → R) :
    (LiftRing.mk (QuarticSearch.poly c) X)^4 =
      denote (LiftRing.of (QuarticSearch.poly c))
        (LiftRing.mk (QuarticSearch.poly c) X) (reductionData c) := by
  have hzero : LiftRing.mk (QuarticSearch.poly c) (QuarticSearch.poly c) = 0 :=
    LiftRing.mk_eq_zero.mpr (dvd_refl _)
  have hp : QuarticSearch.poly c =
      X^4 + C (c 3)*X^3 + C (c 2)*X^2 + C (c 1)*X + C (c 0) := by
    simp [QuarticSearch.poly, Fin.sum_univ_succ]
    ring
  have hz := congrArg (LiftRing.mk (QuarticSearch.poly c)) hp
  rw [hzero] at hz
  simp only [map_add, map_mul, map_pow] at hz
  simp only [denote, reductionData, Quad.ofFn, map_neg, LiftRing.of, RingHom.comp_apply]
  linear_combination -hz

theorem quotientDenote_add (c : Fin 4 → R) (a b : Quad R) :
    quotientDenote c (add a b) = quotientDenote c a + quotientDenote c b :=
  denote_add _ _ _ _

theorem quotientDenote_neg (c : Fin 4 → R) (a : Quad R) :
    quotientDenote c (a.map Neg.neg) = -quotientDenote c a := by
  simp only [quotientDenote, denote, Quad.map, map_neg]
  ring

theorem quotientDenote_const (c : Fin 4 → R) (r : R) :
    quotientDenote c (⟨r, 0, 0, 0⟩ : Quad R) = LiftRing.of (QuarticSearch.poly c) r := by
  simp [quotientDenote, denote]

theorem quotientDenote_mul (c : Fin 4 → R) (a b : Quad R) :
    quotientDenote c (mul (reductionData c) a b) = quotientDenote c a * quotientDenote c b :=
  denote_mul _ _ _ _ _ (quotient_root c)

variable (p μ : ℕ) [Fact p.Prime]

def binaryConst (r : ZMod (p^μ)) : Quad (Word (SubexpLiftRing.baseWidth p μ)) :=
  ⟨encodeWord p μ r, encodeWord p μ 0, encodeWord p μ 0, encodeWord p μ 0⟩

def binaryZero : Quad (Word (SubexpLiftRing.baseWidth p μ)) := binaryConst p μ 0

def binaryOne : Quad (Word (SubexpLiftRing.baseWidth p μ)) := binaryConst p μ 1

theorem binaryConst_quotient (c : Fin 4 → ZMod (p^μ)) (r : ZMod (p^μ)) :
    quotientDenote c ((binaryConst p μ r).map (wordValue p μ)) =
      LiftRing.of (QuarticSearch.poly c) r := by
  simp only [binaryConst, Quad.map, wordValue_encodeWord]
  exact quotientDenote_const c r

theorem binaryZero_quotient (c : Fin 4 → ZMod (p^μ)) :
    quotientDenote c ((binaryZero p μ).map (wordValue p μ)) = 0 := by
  simpa only [binaryZero, map_zero] using binaryConst_quotient p μ c 0

theorem binaryOne_quotient (c : Fin 4 → ZMod (p^μ)) :
    quotientDenote c ((binaryOne p μ).map (wordValue p μ)) = 1 := by
  simpa only [binaryOne, map_one] using binaryConst_quotient p μ c 1

theorem binaryAdd_quotient (c : Fin 4 → ZMod (p^μ))
    (a b : Quad (Word (SubexpLiftRing.baseWidth p μ))) :
    quotientDenote c (((binaryAdd p μ a b).1).map (wordValue p μ)) =
      quotientDenote c (a.map (wordValue p μ)) + quotientDenote c (b.map (wordValue p μ)) := by
  rw [binaryAdd_correct, quotientDenote_add]

theorem binaryNeg_quotient (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (SubexpLiftRing.baseWidth p μ))) :
    quotientDenote c (((binaryNeg p μ a).1).map (wordValue p μ)) =
      -quotientDenote c (a.map (wordValue p μ)) := by
  rw [binaryNeg_correct, quotientDenote_neg]

/-- Only the four supplied coefficients are stored; selection of the
defining polynomial is supplied by `QuarticSearch.liftedCoefficients`. -/
def reductionWords (c : Fin 4 → ZMod (p^μ)) : Quad (Word (SubexpLiftRing.baseWidth p μ)) :=
  (reductionData c).map (encodeWord p μ)

@[simp] theorem reductionWords_value (c : Fin 4 → ZMod (p^μ)) :
    (reductionWords p μ c).map (wordValue p μ) = reductionData c := by
  simp only [reductionWords, Quad.map, reductionData, Quad.ofFn, wordValue_encodeWord]

/-- This is refinement into the exact polynomial quotient whose coefficients
are input data, rather than a separate existentially chosen isomorphic field. -/
theorem binaryMul_quotient (c : Fin 4 → ZMod (p^μ))
    (a b : Quad (Word (SubexpLiftRing.baseWidth p μ))) :
    quotientDenote c (((binaryMul p μ (reductionWords p μ c) a b).1).map (wordValue p μ)) =
      quotientDenote c (a.map (wordValue p μ)) * quotientDenote c (b.map (wordValue p μ)) := by
  rw [binaryMul_correct, reductionWords_value, quotientDenote_mul]

theorem selected_binaryMul_quotient
    (a b : Quad (Word (SubexpLiftRing.baseWidth p μ))) :
    quotientDenote (QuarticSearch.liftedCoefficients p μ)
      (((binaryMul p μ (reductionWords p μ (QuarticSearch.liftedCoefficients p μ)) a b).1).map
        (wordValue p μ)) =
      quotientDenote (QuarticSearch.liftedCoefficients p μ) (a.map (wordValue p μ)) *
      quotientDenote (QuarticSearch.liftedCoefficients p μ) (b.map (wordValue p μ)) :=
  binaryMul_quotient p μ _ a b

end QuotientRefinement

end SubexponentialSAT.SubexpQuarticRing

end OAI.Algorithms
