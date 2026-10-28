import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialConstructor
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAddCall
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatNeg
import OAI.Algorithms.SubexponentialSAT.SubexpLinearFactorEncoding

namespace OAI.Algorithms

/-! Concrete local linear-factor construction. Both scalar arithmetic
operations are calls to fixed, proved bit programs. The resulting polynomial
is padded to the runtime dimension and stored in cache 241.
-/

namespace SubexponentialSAT.SubexpLocalLinearFactorProgram

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective 8 8⟩
def addPorts : Fin 20 ↪ Fin 256 := ⟨Fin.castAdd 236, Fin.castAdd_injective 20 236⟩
def negatePorts : Fin 24 ↪ Fin 256 :=
  ⟨![20,21,22,23,211,25,26,27,28,29,30,31,32,33,5,35,36,37,218,219,10,41,42,43], by decide⟩

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def scalarNegate : Code := SubexpQuarticFlatNeg.callAt registers negatePorts
def scalarAdd : Code := SubexpFlatAddCall.callAt registers addPorts

def command : Code :=
  scalarNegate ;; copy 213 8 ;; copy 219 9 ;; scalarAdd ;;
    SubexpPolynomialConstructor.move 8 100 ;; copy 207 101 ;;
    SubexpPolynomialConstructor.constructAtInputs 241

theorem flat_eq_encode {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatNeg.flat a = SubexpFlatAdd.encode a := by
  simp [SubexpQuarticFlatNeg.flat, SubexpQuarticFlatNeg.wordLists,
    FourWordPrograms.flatWords, SubexpFlatAdd.encode, SubexpFlatAdd.flatten,
    SubexpFlatAdd.quadWords, Quad.toFn]

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def negative (minusOne : Word (baseWidth p μ))
    (c : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) :=
  SubexpQuarticNegMachine.negateWords p μ M minusOne c

def difference (minusOne : Word (baseWidth p μ))
    (theta c : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) :=
  (SubexpPreparedQuartic.binaryAdd p μ M theta (negative p μ M minusOne c)).1

def factor (minusOne : Word (baseWidth p μ))
    (zero theta c one : Quad (Word (baseWidth p μ))) (D : ℕ) :=
  SubexpLocalCorrectionAlgebra.padded zero (difference p μ M minusOne theta c) one D

@[simp] theorem factor_length (minusOne : Word (baseWidth p μ))
    (zero theta c one : Quad (Word (baseWidth p μ))) (D : ℕ) :
    (factor p μ M minusOne zero theta c one D).length = D :=
  SubexpLocalCorrectionAlgebra.padded_length _ _ _ _

theorem difference_denote (reduction : Fin 4 → ZMod (p^μ))
    (minusOne : Word (baseWidth p μ)) (hminus : wordValue p μ minusOne = -1)
    (theta c : Quad (Word (baseWidth p μ))) :
    quotientDenote reduction ((difference p μ M minusOne theta c).map (wordValue p μ)) =
      quotientDenote reduction (theta.map (wordValue p μ)) -
        quotientDenote reduction (c.map (wordValue p μ)) := by
  rw [difference, SubexpPreparedQuartic.binaryAdd_quotient]
  rw [negative, SubexpQuarticNegMachine.negateWords_quotient p μ M minusOne c hminus]
  exact (sub_eq_add_neg _ _).symm

theorem factor_encode (minusOne : Word (baseWidth p μ))
    (zero theta c one : Quad (Word (baseWidth p μ))) (D : ℕ)
    (hz : SubexpFlatAdd.encode zero = List.replicate (4 * baseWidth p μ) false) :
    SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode
      (factor p μ M minusOne zero theta c one D) =
      SubexpLinearFactorProgram.paddedBits (baseWidth p μ)
        (SubexpFlatAdd.encode (difference p μ M minusOne theta c)) (SubexpFlatAdd.encode one) D :=
  SubexpLinearFactorEncoding.encode_padded SubexpFlatAdd.encode zero _ one _ D hz

theorem factor_denote (reduction : Fin 4 → ZMod (p^μ))
    (minusOne : Word (baseWidth p μ)) (hminus : wordValue p μ minusOne = -1)
    (zero theta c one : Quad (Word (baseWidth p μ)))
    (hz : quotientDenote reduction (zero.map (wordValue p μ)) = 0)
    (ho : quotientDenote reduction (one.map (wordValue p μ)) = 1) (D : ℕ) :
    PolynomialAlgorithm.denote ((factor p μ M minusOne zero theta c one D).map
      (fun a => quotientDenote reduction (a.map (wordValue p μ)))) =
      Truncation.trunc D (Polynomial.X + Polynomial.C
        (quotientDenote reduction (theta.map (wordValue p μ)) -
          quotientDenote reduction (c.map (wordValue p μ)))) := by
  rw [factor, SubexpLocalCorrectionAlgebra.padded_denote
    (fun a : Quad (Word (baseWidth p μ)) => quotientDenote reduction (a.map (wordValue p μ)))
    zero (difference p μ M minusOne theta c) one hz D,
    difference_denote p μ M reduction minusOne hminus theta c, ho]
  congr 1
  simp [add_comm]

theorem negate_run (s : Store) (c : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (width : List Bool)
    (hw : width.length = baseWidth p μ)
    (hstore : ∀ i, s (negatePorts i) = SubexpQuarticFlatNeg.initialStore c minusOne M.bits width i) :
    ExecutesIn scalarNegate (25000 * (baseWidth p μ + 1)^2) s
      (Function.update s 219 (SubexpFlatAdd.encode (negative p μ M minusOne c))) := by
  intro regs
  obtain ⟨n, rf, hn, he⟩ := SubexpQuarticFlatNeg.callAt_eval registers negatePorts
    p μ M c minusOne width hw (⟨regs, s⟩ : Data) hstore
  exact ⟨n, Function.extend registers rf regs, hn, by
    simpa only [scalarNegate, negative, flat_eq_encode, show negatePorts 19 = 219 from rfl] using he⟩

theorem command_run (s : Store) (D : ℕ)
    (theta c one : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ)) (width : List Bool) (frame : Fin 6 → List Bool)
    (hw : width.length = baseWidth p μ)
    (hneg : ∀ i, s (negatePorts i) = SubexpQuarticFlatNeg.initialStore c minusOne M.bits width i)
    (hadd : ∀ i, s (addPorts i) =
      (SubexpFlatAdd.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (htheta : s 213 = SubexpFlatAdd.encode theta)
    (hone : s 207 = SubexpFlatAdd.encode one)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * baseWidth p μ) false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h241 : s 241 = []) (h245 : s 245 = []) :
    ExecutesIn command (51000 * (D + 1) * (baseWidth p μ + 1)^2) s
      (Function.update
        (Function.update s 219 (SubexpFlatAdd.encode (negative p μ M minusOne c))) 241
        (SubexpLinearFactorProgram.paddedBits (baseWidth p μ)
          (SubexpFlatAdd.encode (difference p μ M minusOne theta c))
          (SubexpFlatAdd.encode one) D)) := by
  let B := baseWidth p μ
  let neg := SubexpFlatAdd.encode (negative p μ M minusOne c)
  let delta := SubexpFlatAdd.encode (difference p μ M minusOne theta c)
  let out := SubexpLinearFactorProgram.paddedBits B delta (SubexpFlatAdd.encode one) D
  let s₁ := Function.update s 219 neg
  let s₂ := Function.update s₁ 8 (SubexpFlatAdd.encode theta)
  let s₃ := Function.update s₂ 9 neg
  let s₄ := Function.update s₁ 8 delta
  let s₅ := Function.update s₁ 100 delta
  let s₆ := Function.update s₅ 101 (SubexpFlatAdd.encode one)
  have h8 : s 8 = [] := by
    simpa [addPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.«stacks»,
      Fin.addCases, Fin.coe_ofNat_eq_mod] using hadd 8
  have h9 : s 9 = [] := by
    simpa [addPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.«stacks»,
      Fin.addCases, Fin.coe_ofNat_eq_mod] using hadd 9
  have h₁ := negate_run p μ M s c minusOne width hw hneg
  have h₂ : ExecutesIn (copy 213 8) (28 * B + 5) s₁ s₂ := by
    have h := copy_run 213 8 s₁ (by decide) (by decide) (by decide) (by simp [s₁, h120])
    simpa [s₁, s₂, htheta, h8, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using h
  have h₃ : ExecutesIn (copy 219 9) (28 * B + 5) s₂ s₃ := by
    have h := copy_run 219 9 s₂ (by decide) (by decide) (by decide)
      (by simp [s₂, s₁, h120])
    simpa [s₂, s₁, s₃, h9, neg, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using h
  have hadd' : ∀ i, s₃ (addPorts i) =
      (SubexpFlatAdd.ready (fun _ => false) M.bits (SubexpFlatAdd.encode theta)
        neg width [] frame).stacks i := by
    intro i
    have h := hadd i
    fin_cases i <;>
      simp [s₃, s₂, s₁, addPorts, SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.«stacks»,
        Fin.addCases, Fin.coe_ofNat_eq_mod] at h ⊢ <;> assumption
  have he₄ : SubexpFlatAddCall.resultStacks addPorts delta s₃ = s₄ := by
    funext j
    by_cases h : j = 9 <;> by_cases hj8 : j = 8 <;>
      simp [SubexpFlatAddCall.resultStacks, addPorts, s₄, s₃, s₂, s₁,
        Function.update_apply, h, hj8, h9]
  have h₄ : ExecutesIn scalarAdd (25000 * (B + 1)^2) s₃ s₄ := by
    intro regs
    obtain ⟨n, rf, hn, he⟩ := SubexpFlatAddCall.callAt_eval registers addPorts p μ M
      theta (negative p μ M minusOne c) width hw (⟨regs, s₃⟩ : Data) frame hadd'
    refine ⟨n, Function.extend registers rf regs, hn, ?_⟩
    change Eval scalarAdd n _ ⟨_, SubexpFlatAddCall.resultStacks addPorts delta s₃⟩ at he
    rw [he₄] at he
    exact he
  have he₅ : Function.update (Function.update s₄ 8 []) 100 (s₄ 8) = s₅ := by
    funext j
    by_cases h : j = 8 <;> simp [s₄, s₅, s₁, Function.update_apply, h, h8]
  have h₅ : ExecutesIn (SubexpPolynomialConstructor.move 8 100) (24 * B + 6) s₄ s₅ := by
    have h := SubexpPolynomialConstructor.move_run s₄ 8 100 (by decide) (by decide)
      (by decide) (by simp [s₄, s₁, h245]) (by simp [s₄, s₁, h100])
    rw [he₅] at h
    simpa [s₄, delta, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using h
  have h₆ : ExecutesIn (copy 207 101) (28 * B + 5) s₅ s₆ := by
    have h := copy_run 207 101 s₅ (by decide) (by decide) (by decide)
      (by simp [s₅, s₁, h120])
    simpa [s₆, s₅, s₁, hone, h101, SubexpFlatAdd.encode_length, B, ← Nat.mul_assoc] using h
  have he₇ : Function.update (Function.update (Function.update s₆ 100 []) 101 []) 241 out =
      Function.update s₁ 241 out := by
    funext j
    by_cases h100' : j = 100 <;> by_cases h101' : j = 101 <;>
      simp [s₆, s₅, s₁, Function.update_apply, h100, h101, h100', h101']
  have h₇ : ExecutesIn (SubexpPolynomialConstructor.constructAtInputs 241)
      (150 * (D + 1) * (B + 1)) s₆ (Function.update s₁ 241 out) := by
    have h := SubexpPolynomialConstructor.constructAtInputs_run s₆ 241 (by decide) (by decide)
      D B delta (SubexpFlatAdd.encode one) (by simp [s₆, s₅]) (by simp [s₆])
      (SubexpFlatAdd.encode_length _) (SubexpFlatAdd.encode_length _)
      (by simp [s₆, s₅, s₁, hD]) (by simp [s₆, s₅, s₁, hzero, B])
      (by simp [s₆, s₅, s₁, h102]) (by simp [s₆, s₅, s₁, h107])
      (by simp [s₆, s₅, s₁, h108]) (by simp [s₆, s₅, s₁, h120])
      (by simp [s₆, s₅, s₁, h245]) (by simp [s₆, s₅, s₁, h241])
    change ExecutesIn _ _ _ (Function.update (Function.update (Function.update s₆ 100 []) 101 []) 241 out) at h
    rw [he₇] at h
    exact h
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq h₇)))))
  apply h.mono
  change 25000 * (B + 1)^2 + _ ≤ 51000 * (D + 1) * (B + 1)^2
  ring_nf
  omega

end SubexponentialSAT.SubexpLocalLinearFactorProgram

end OAI.Algorithms
