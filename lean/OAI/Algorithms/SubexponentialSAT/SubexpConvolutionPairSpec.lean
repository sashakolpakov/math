import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionPair
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionRows
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionEncoding

namespace OAI.Algorithms

/-! Concrete instantiation of the convolution controller's local pair
contract. The base contains only static arithmetic data and empty work space;
the eleven controller buffers may vary on every invocation. -/

namespace SubexponentialSAT.SubexpConvolutionPairSpec

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem buffers_below (base : Store) (w : Buffers) (j : Fin 256) (hj : j.val < 100) :
    buffers base w j = base j := by
  apply buffers_frame
  rintro ⟨i, hi⟩
  have hv := congrArg (fun i : Fin 256 => i.val) hi
  fin_cases i <;> simp [bufferPorts] at hv <;> omega

theorem buffers_high (base : Store) (w : Buffers) (j : Fin 77)
    (h70 : j ≠ 70) (h71 : j ≠ 71) :
    buffers base w (SubexpConvolutionPair.highPort j) =
      base (SubexpConvolutionPair.highPort j) := by
  apply buffers_frame
  rintro ⟨i, hi⟩
  have hv := congrArg (fun i : Fin 256 => i.val) hi
  fin_cases i <;> simp [bufferPorts, SubexpConvolutionPair.highPort] at hv <;> omega

theorem buffers_work (base : Store) (w : Buffers) (j : Fin 256)
    (hlo : 112 ≤ j.val) (hhi : j.val ≤ 119) : buffers base w j = base j := by
  apply buffers_frame
  rintro ⟨i, hi⟩
  have hv := congrArg (fun i : Fin 256 => i.val) hi
  fin_cases i <;> simp [bufferPorts] at hv <;> omega

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

structure BaseReady (base : Store) (t : Quad (Word (baseWidth p μ)))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool) : Prop where
  high : ∀ j : Fin 77, j ≠ 70 → j ≠ 71 →
    base (SubexpConvolutionPair.highPort j) =
      SubexpQuarticFlatMul.bankStore (fun _ => []) M.bits
        (SubexpQuarticFlatMul.flat t) scalarWidth [] j
  low : ∀ i : Fin 20,
    base (SubexpConvolutionPair.lowPort (SubexpJetCellProgram.scalarPorts i)) =
      (SubexpFlatAdd.ready (fun _ => false) M.bits [] [] scalarWidth [] frame).stacks i
  width : (base 104).length = 4 * baseWidth p μ
  scalarWidthLength : scalarWidth.length = baseWidth p μ
  work : ∀ j : Fin 256, 112 ≤ j.val → j.val ≤ 119 → base j = []

def add (a b : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) :=
  (SubexpPreparedQuartic.binaryAdd p μ M a b).1

def mul (t a b : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) :=
  (SubexpPreparedQuartic.binaryMul p μ M t a b).1

/-- Every varying controller buffer receives the same actual fixed pair
program. The only side condition on the base is its concrete static layout. -/
theorem pairSpec (base : Store) (t : Quad (Word (baseWidth p μ)))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : BaseReady p μ M base t scalarWidth frame) (D : ℕ) :
    PairSpec SubexpConvolutionPair.command base SubexpFlatAdd.encode
      (add p μ M) (mul p μ M t) D
      (500000 * (D + 1) * (baseWidth p μ + 1)^2) := by
  intro w a b acc hlen hi hacc ha hb regs
  have hin : (w 3).length < acc.length := by omega
  obtain ⟨earlier, c, rest, hearlier, hrows, hsplit, hnext⟩ :=
    SubexpConvolutionEncoding.encode_addProduct_split SubexpFlatAdd.encode
      (4 * baseWidth p μ) (fun c => SubexpFlatAdd.encode_length c)
      (add p μ M) (mul p μ M t) acc (w 3).length a b hin
  let d : Data := ⟨regs, buffers base w⟩
  have hready : SubexpConvolutionPair.Ready p μ M d t a b c earlier rest
      (base 104) (w 3) scalarWidth frame := by
    constructor
    · intro j
      by_cases hj70 : j = 70
      · subst j
        simpa [d, SubexpConvolutionPair.highPort, SubexpQuarticFlatMul.initialStore,
          SubexpQuarticFlatMul.bankStore, SubexpConvolutionPair.flat_eq_encode] using ha
      · by_cases hj71 : j = 71
        · subst j
          simpa [d, SubexpConvolutionPair.highPort, SubexpQuarticFlatMul.initialStore,
            SubexpQuarticFlatMul.bankStore, SubexpConvolutionPair.flat_eq_encode] using hb
        · change buffers base w (SubexpConvolutionPair.highPort j) = _
          rw [buffers_high base w j hj70 hj71]
          simpa [SubexpQuarticFlatMul.initialStore, hj70, hj71] using H.high j hj70 hj71
    · intro i
      change buffers base w (SubexpConvolutionPair.lowPort
        (SubexpJetCellProgram.scalarPorts i)) = _
      rw [buffers_below base w _ (by
        dsimp [SubexpConvolutionPair.lowPort, SubexpJetCellProgram.scalarPorts]
        have := i.isLt
        omega)]
      exact H.low i
    · change buffers base w 102 = _
      rw [buffers_102, hacc]
      exact hsplit
    · exact buffers_103 base w
    · exact hearlier.symm
    · exact buffers_104 base w
    · exact H.width
    · simpa only [H.width] using hrows
    · exact H.scalarWidthLength
    · intro j hlo hhi
      change buffers base w j = []
      rw [buffers_work base w j hlo hhi]
      exact H.work j hlo hhi
  obtain ⟨n, e, hn, he, hs, _⟩ := SubexpConvolutionPair.command_eval p μ M d t a b c
    earlier rest (base 104) (w 3) scalarWidth frame hready
  have hfinal : e.stacks = buffers base
      (Function.update (Function.update (Function.update w 9 []) 10 []) 2
        (encodeArray SubexpFlatAdd.encode
          (TruncatedConvolution.addProduct (add p μ M) (mul p μ M t)
            (w 3).length a b acc))) := by
    rw [hs, buffers_update, buffers_update, buffers_update]
    change Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
        102 (earlier.flatten ++
          (SubexpFlatAdd.encode (SubexpConvolutionPair.result p μ M t a b c) ++ rest)) =
      Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
        102 (encodeArray SubexpFlatAdd.encode
          (TruncatedConvolution.addProduct (add p μ M) (mul p μ M t)
            (w 3).length a b acc))
    exact congrArg
      (fun record : List Bool =>
        Function.update (Function.update (Function.update (buffers base w) 198 []) 199 [])
          102 record) hnext.symm
  refine ⟨n, e.regs, hn.trans ?_, ?_⟩
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : (w 3).length + 1 ≤ D + 1))
  · have heq : e = (⟨e.regs, buffers base
        (Function.update (Function.update (Function.update w 9 []) 10 []) 2
          (encodeArray SubexpFlatAdd.encode
            (TruncatedConvolution.addProduct (add p μ M) (mul p μ M t)
              (w 3).length a b acc)))⟩ : Data) := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · exact hfinal
    rw [heq] at he
    exact he

end SubexponentialSAT.SubexpConvolutionPairSpec

end OAI.Algorithms
