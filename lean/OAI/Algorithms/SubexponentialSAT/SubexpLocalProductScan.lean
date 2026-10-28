import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalProductProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl

namespace OAI.Algorithms

/-! The flat node scanner instantiated with the concrete polynomial
factor/power service. Every component premise below describes stored words
or empty work space; no arithmetic-execution oracle remains.
-/

namespace SubexponentialSAT.SubexpLocalProductScan

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D

structure Ready (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool)
    (frame : Fin 6 → List Bool) : Prop where
  multiply : SubexpConvolutionPairSpec.BaseReady p (D + 1) M s t width frame
  add : ∀ i, s (SubexpLocalLinearFactorProgram.addPorts i) =
    (SubexpFlatAdd.ready (fun _ => false) M.bits [] [] width [] frame).stacks i
  negate : ∀ c : Coeff p D, ∀ i,
    (Function.update s 218 (SubexpFlatAdd.encode c)) (SubexpLocalLinearFactorProgram.negatePorts i) =
      SubexpQuarticFlatNeg.initialStore c minusOne M.bits width i
  buffers : ∀ i, s (bufferPorts i) = []
  scratch : ∀ i ∈ ([107,120,121,122,219,241,244,245,246] : List (Fin 256)), s i = []
  theta : s 213 = SubexpFlatAdd.encode theta
  one : s 207 = SubexpFlatAdd.encode one
  dimension : s 243 = List.replicate D true
  zeroCell : s 104 = List.replicate (4 * baseWidth p (D + 1)) false
  zeroCode : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false
  zeroArray : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z)

theorem scan_below {A C : Type*} (base : Store) (enc : C → List Bool) (encA : A → List Bool)
    (cs : List C) (x : SubexpNodeScanControl.Cursor A) (current negative : List Bool)
    (j : Fin 256) (hj : j.val < 205) :
    SubexpNodeScanControl.ready base enc encA cs x current negative j = base j := by
  apply SubexpNodeScanControl.work_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  fin_cases i <;> norm_num [SubexpNodeScanControl.ports, Fin.coe_ofNat_eq_mod] at hv <;> omega

theorem scan_frame {A C : Type*} (base : Store) (enc : C → List Bool) (encA : A → List Bool)
    (cs : List C) (x : SubexpNodeScanControl.Cursor A) (current negative : List Bool)
    (j : Fin 256) (hj : ¬ ∃ i, SubexpNodeScanControl.ports i = j) :
    SubexpNodeScanControl.ready base enc encA cs x current negative j = base j :=
  SubexpNodeScanControl.work_frame base _ j hj

theorem negate_frame (i : Fin 24) (h18 : i ≠ 18) (h19 : i ≠ 19) :
    ¬ ∃ j, SubexpNodeScanControl.ports j = SubexpLocalLinearFactorProgram.negatePorts i := by
  fin_cases i <;> try contradiction
  all_goals decide

def stepValue (t z theta one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (P : Poly p D) (c : Coeff p D) : Poly p D :=
  SubexpLocalProductProgram.value p (D + 1) M t z theta c one minusOne P

theorem includeSpec (base : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : Ready p D M base t z theta one minusOne width frame) :
    SubexpNodeScanControl.IncludeSpec SubexpLocalProductProgram.command base SubexpFlatAdd.encode
      (encode p (D + 1))
      (fun c => SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne c))
      (stepValue p D M t z theta one minusOne)
      (700000 * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2) := by
  intro cs x c
  let before := SubexpNodeScanControl.ready base SubexpFlatAdd.encode (encode p (D + 1))
    cs x (SubexpFlatAdd.encode c) []
  have below : ∀ j : Fin 256, j.val < 205 → before j = base j :=
    scan_below base _ _ cs x _ _
  have frames (j : Fin 256) (hj : ¬ ∃ i, SubexpNodeScanControl.ports i = j) : before j = base j :=
    scan_frame base _ _ cs x _ _ j hj
  have hneg : ∀ i, before (SubexpLocalLinearFactorProgram.negatePorts i) =
      SubexpQuarticFlatNeg.initialStore c minusOne M.bits width i := by
    intro i
    by_cases h18 : i = 18
    · subst i
      simpa [before, SubexpNodeScanControl.ready, SubexpNodeScanControl.words,
        SubexpLocalLinearFactorProgram.negatePorts] using H.negate c 18
    · by_cases h19 : i = 19
      · subst i
        simpa [before, SubexpNodeScanControl.ready, SubexpNodeScanControl.words,
          SubexpLocalLinearFactorProgram.negatePorts, H.scratch 219 (by decide)] using H.negate c 19
      · rw [frames _ (negate_frame i h18 h19)]
        have hn : SubexpLocalLinearFactorProgram.negatePorts i ≠ 218 := by
          intro he
          apply h18
          apply SubexpLocalLinearFactorProgram.negatePorts.injective
          exact he
        simpa [hn] using H.negate c i
  have hadd : ∀ i, before (SubexpLocalLinearFactorProgram.addPorts i) =
      (SubexpFlatAdd.ready (fun _ => false) M.bits [] [] width [] frame).stacks i := by
    intro i
    rw [below _ (by
      dsimp [SubexpLocalLinearFactorProgram.addPorts]
      have := i.isLt
      omega)]
    exact H.add i
  have h := SubexpLocalProductProgram.command_value p (D + 1) M before D x.value
    t z theta c one minusOne width frame H.multiply.scalarWidthLength hneg hadd
    (baseReady_congr p (D + 1) M base before t width frame below H.multiply)
    (fun i => by rw [below _ (bufferPorts_lt i)]; exact H.buffers i)
    (by rw [below 120 (by decide)]; exact H.scratch 120 (by decide))
    (by rw [below 121 (by decide)]; exact H.scratch 121 (by decide))
    (by rw [below 122 (by decide)]; exact H.scratch 122 (by decide))
    (by rw [below 107 (by decide)]; exact H.scratch 107 (by decide))
    (by rw [frames 244 (by decide)]; exact H.scratch 244 (by decide))
    (by rw [frames 245 (by decide)]; exact H.scratch 245 (by decide))
    (by rw [frames 246 (by decide)]; exact H.scratch 246 (by decide))
    (by rw [frames 241 (by decide)]; exact H.scratch 241 (by decide))
    (by rw [frames 213 (by decide)]; exact H.theta)
    (by rw [frames 207 (by decide)]; exact H.one)
    (by rw [frames 243 (by decide)]; exact H.dimension)
    (by rw [below 104 (by decide)]; exact H.zeroCell) H.zeroCode
    (by rw [frames 242 (by decide)]; exact H.zeroArray)
    (by simp [before, SubexpNodeScanControl.ready, SubexpNodeScanControl.words])
  have he : Function.update (Function.update before 219
      (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne c)))
      240 (encode p (D + 1) (stepValue p D M t z theta one minusOne x.value c)) =
      SubexpNodeScanControl.ready base SubexpFlatAdd.encode (encode p (D + 1)) cs
        {x with value := stepValue p D M t z theta one minusOne x.value c}
        (SubexpFlatAdd.encode c)
        (SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne c)) := by
    change Function.update (Function.update (SubexpNodeScanControl.work base _)
      (SubexpNodeScanControl.ports 5) _) (SubexpNodeScanControl.ports 3) _ =
      SubexpNodeScanControl.work base _
    rw [← SubexpNodeScanControl.work_update, ← SubexpNodeScanControl.work_update]
    apply congrArg (SubexpNodeScanControl.work base)
    funext j
    fin_cases j <;> simp [SubexpNodeScanControl.words]
  dsimp only [stepValue] at he
  rw [he] at h
  exact h

/-- Actual node traversal with the concrete arithmetic service, starting
from any fixed-D accumulator. The remaining counter/marker are explicit in
the final cursor; final local-CRT cleanup removes them. -/
theorem command_value (base : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : Ready p D M base t z theta one minusOne width frame)
    (cs : List (Coeff p D)) (x : SubexpNodeScanControl.Cursor (Poly p D)) :
    ExecutesIn (SubexpNodeScanControl.command SubexpLocalProductProgram.command)
      (cs.length * (700000 * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2 +
        18 * (4 * baseWidth p (D + 1)) + 28) + 2)
      (SubexpNodeScanControl.ready base SubexpFlatAdd.encode (encode p (D + 1)) cs x [] [])
      (SubexpNodeScanControl.ready base SubexpFlatAdd.encode (encode p (D + 1)) ([] : List (Coeff p D))
        (SubexpNodeScanControl.run (stepValue p D M t z theta one minusOne) cs x) [] []) := by
  apply SubexpNodeScanControl.command_run SubexpLocalProductProgram.command base _ _
    (fun c => SubexpFlatAdd.encode (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne c))
    (stepValue p D M t z theta one minusOne) _ _
    (includeSpec p D M base t z theta one minusOne width frame H)
    (fun c => SubexpFlatAdd.encode_length c)
  · exact Nat.mul_pos (by decide) (Nat.mul_pos (Nat.zero_lt_succ D) (Nat.zero_lt_succ _))
  · intro c
    exact le_of_eq (SubexpFlatAdd.encode_length _)
  · exact H.multiply.width
  · exact H.scratch 121 (by decide)
  · exact H.scratch 122 (by decide)

end SubexponentialSAT.SubexpLocalProductScan

end OAI.Algorithms
