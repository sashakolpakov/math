import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDecodedCount

namespace OAI.Algorithms

/-!
# Uniqueness of canonical encoded quartic coefficients

Semantic equality determines identical bytes when every coefficient word is
strictly below the prime-power modulus. The arithmetic callbacks normalize
their outputs, so different finite summation orders can use this criterion.
-/

namespace SubexponentialSAT.SubexpCanonicalWords

open BinaryArithmetic SubexpLiftRing SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime]

def CanonicalWord (x : Word (baseWidth p μ)) : Prop := BinaryArithmetic.toNat x.val < p^μ

def CanonicalQuad (a : Quad (Word (baseWidth p μ))) : Prop :=
  CanonicalWord p μ a.c0 ∧ CanonicalWord p μ a.c1 ∧
    CanonicalWord p μ a.c2 ∧ CanonicalWord p μ a.c3

omit [Fact p.Prime] in
theorem word_eq_of_value_eq (x y : Word (baseWidth p μ))
    (hx : CanonicalWord p μ x) (hy : CanonicalWord p μ y)
    (hvalue : wordValue p μ x = wordValue p μ y) : x = y := by
  apply Subtype.ext
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · exact x.property.trans y.property.symm
  · exact SubexpDecodedCount.raw_eq_of_canonical p μ x.val (BinaryArithmetic.toNat y.val) hx hy hvalue

omit [Fact p.Prime] in
theorem quad_eq_of_values_eq (a b : Quad (Word (baseWidth p μ)))
    (ha : CanonicalQuad p μ a) (hb : CanonicalQuad p μ b)
    (hvalue : a.map (wordValue p μ) = b.map (wordValue p μ)) : a = b := by
  have h0 := word_eq_of_value_eq p μ a.c0 b.c0 ha.1 hb.1 (congrArg Quad.c0 hvalue)
  have h1 := word_eq_of_value_eq p μ a.c1 b.c1 ha.2.1 hb.2.1 (congrArg Quad.c1 hvalue)
  have h2 := word_eq_of_value_eq p μ a.c2 b.c2 ha.2.2.1 hb.2.2.1 (congrArg Quad.c2 hvalue)
  have h3 := word_eq_of_value_eq p μ a.c3 b.c3 ha.2.2.2 hb.2.2.2 (congrArg Quad.c3 hvalue)
  cases a
  cases b
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

theorem quad_eq_of_quotient_eq (hμ : 0 < μ) (c : Fin 4 → ZMod (p^μ))
    (a b : Quad (Word (baseWidth p μ)))
    (ha : CanonicalQuad p μ a) (hb : CanonicalQuad p μ b)
    (hvalue : quotientDenote c (a.map (wordValue p μ)) =
      quotientDenote c (b.map (wordValue p μ))) : a = b := by
  let : Fact (1 < p^μ) := ⟨SubexpQuarticEncoding.primePower_one_lt p μ hμ⟩
  exact quad_eq_of_values_eq p μ a b ha hb
    (SubexpQuarticEncoding.quotientDenote_injective c hvalue)

theorem literalZero_canonical :
    CanonicalWord p μ (SubexpPreparedQuartic.literalWordRun p μ []).1 := by
  change BinaryArithmetic.toNat (SubexpModulusConstruction.normalizeRun _ []).1 < p^μ
  rw [SubexpModulusConstruction.normalizeRun_value]
  · exact pow_pos (Fact.out : p.Prime).pos μ
  · exact Nat.two_pow_pos _

theorem literalOne_canonical (hμ : 0 < μ) :
    CanonicalWord p μ (SubexpPreparedQuartic.literalWordRun p μ [true]).1 := by
  change BinaryArithmetic.toNat (SubexpModulusConstruction.normalizeRun _ [true]).1 < p^μ
  have hB : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.zero_lt_succ _)
  rw [SubexpModulusConstruction.normalizeRun_value]
  · exact SubexpQuarticEncoding.primePower_one_lt p μ hμ
  · exact Nat.one_lt_pow (Nat.ne_of_gt hB) Nat.one_lt_two

theorem prepareZero_canonical :
    CanonicalQuad p μ (SubexpPreparedQuartic.prepareZero p μ).1 :=
  ⟨literalZero_canonical p μ, literalZero_canonical p μ,
    literalZero_canonical p μ, literalZero_canonical p μ⟩

theorem prepareOne_canonical (hμ : 0 < μ) :
    CanonicalQuad p μ (SubexpPreparedQuartic.prepareOne p μ).1 :=
  ⟨literalOne_canonical p μ hμ, literalZero_canonical p μ,
    literalZero_canonical p μ, literalZero_canonical p μ⟩

variable (M : SubexpPreparedQuartic.Modulus p μ)

theorem wordAdd_canonical (x y : Word (baseWidth p μ)) :
    CanonicalWord p μ (SubexpPreparedQuartic.wordAdd p μ M x y).1 :=
  SubexpPreparedQuartic.wordAdd_canonical p μ M x y

theorem wordMul_canonical (x y : Word (baseWidth p μ)) :
    CanonicalWord p μ (SubexpPreparedQuartic.wordMul p μ M x y).1 := by
  change BinaryArithmetic.toNat (mulBaseRun _ _ _ _).1 < p^μ
  rw [mulBaseRun_value]
  · rw [M.value]
    exact Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos μ)
  · rw [M.value]
    exact pow_pos (Fact.out : p.Prime).pos μ
  · rw [M.value]
    exact modulus_le_width p μ

theorem wordNeg_canonical (x : Word (baseWidth p μ)) :
    CanonicalWord p μ (SubexpPreparedQuartic.wordNeg p μ M x).1 := by
  have hpos : 0 < BinaryArithmetic.toNat M.bits := by
    rw [M.value]
    exact pow_pos (Fact.out : p.Prime).pos μ
  have hcap : BinaryArithmetic.toNat M.bits ≤ 2^baseWidth p μ := by
    rw [M.value]
    exact modulus_le_width p μ
  let reduced := (SubexpPreparedQuartic.wordAdd p μ M x
    (SubexpPreparedQuartic.zeroWord p μ)).1
  have hred : BinaryArithmetic.toNat reduced.val < BinaryArithmetic.toNat M.bits := by
    rw [M.value]
    exact wordAdd_canonical p μ M x (SubexpPreparedQuartic.zeroWord p μ)
  have hv := SubexpBaseNegation.negBaseRun_value (baseWidth p μ) M.bits reduced.val
    M.length_le reduced.property.le hpos hcap hred
  change BinaryArithmetic.toNat (SubexpBaseNegation.negBaseRun _ _ _).1 < p^μ
  rw [hv, ← M.value]
  exact Nat.mod_lt _ hpos

theorem binaryAdd_canonical (a b : Quad (Word (baseWidth p μ))) :
    CanonicalQuad p μ (SubexpPreparedQuartic.binaryAdd p μ M a b).1 :=
  ⟨wordAdd_canonical p μ M a.c0 b.c0,
    wordAdd_canonical p μ M a.c1 b.c1,
    wordAdd_canonical p μ M a.c2 b.c2,
    wordAdd_canonical p μ M a.c3 b.c3⟩

theorem binaryMul_canonical (t a b : Quad (Word (baseWidth p μ))) :
    CanonicalQuad p μ (SubexpPreparedQuartic.binaryMul p μ M t a b).1 := by
  unfold SubexpPreparedQuartic.binaryMul SubexpQuarticRing.mulRun
  exact binaryAdd_canonical p μ M _ _

theorem binaryNeg_canonical (a : Quad (Word (baseWidth p μ))) :
    CanonicalQuad p μ (SubexpPreparedQuartic.binaryNeg p μ M a).1 :=
  ⟨wordNeg_canonical p μ M a.c0, wordNeg_canonical p μ M a.c1,
    wordNeg_canonical p μ M a.c2, wordNeg_canonical p μ M a.c3⟩

end SubexponentialSAT.SubexpCanonicalWords

end OAI.Algorithms
