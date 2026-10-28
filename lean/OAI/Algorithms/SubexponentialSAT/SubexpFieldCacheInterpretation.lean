import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheAlgebra
import OAI.Algorithms.SubexponentialSAT.SubexpNodeLiftData

namespace OAI.Algorithms

/-! The cache entries in the exact node order produced by the field machine. -/

namespace SubexponentialSAT.SubexpFieldCacheInterpretation

open SubexpLiftRing SubexpQuarticRing SubexpActualRing
open SubexpFieldCacheNodeLoop (PowerValue)
open SubexpFieldCachePairLoop (PairValue)
open SubexpFieldCacheProgram (negativeWords)

variable (p : ℕ) [Fact p.Prime]

noncomputable def ringValue (a : Quad (Word (baseWidth p 1))) : Ring p 1 :=
  quotientDenote (QuarticSearch.liftedCoefficients p 1) (a.map (wordValue p 1))

noncomputable def fieldValue (a : Quad (Word (baseWidth p 1))) : E p :=
  rho p 1 (by decide) (ringValue p a)

theorem sourceQuad_ringValue (c : SubexpFieldNodes.Coefficients p) :
    ringValue p (SubexpNodeLiftData.sourceQuad p c) =
      sectionValue p 1 (by decide) (SubexpFieldNodes.interpret p c) := by
  have hv : (SubexpNodeLiftData.sourceQuad p c).map (wordValue p 1) =
      SubexpFieldNodes.liftQuad p 1 c := by
    simp [SubexpNodeLiftData.sourceQuad, Quad.map]
  unfold ringValue
  rw [hv]
  exact SubexpFieldNodes.quotientDenote_liftQuad p 1 (by decide) c

theorem sourceQuad_fieldValue (c : SubexpFieldNodes.Coefficients p) :
    fieldValue p (SubexpNodeLiftData.sourceQuad p c) = SubexpFieldNodes.interpret p c := by
  simp only [fieldValue, sourceQuad_ringValue, rho_sectionValue]

theorem node_value (i : Fin (p^4 - 1)) :
    fieldValue p (SubexpNodeLiftData.sourceQuad p (SubexpMachineNodeOrder.nodeCoefficients p i)) =
      (SubexpMachineNodeOrder.nodeEquiv p i).val := by
  rw [sourceQuad_fieldValue, SubexpMachineNodeOrder.node_value]

theorem nodeQuads_length : (SubexpNodeLiftData.nodeQuads p).length = p^4 - 1 := by
  simp [SubexpNodeLiftData.nodeQuads]

theorem nodeQuads_get (i : Fin (p^4 - 1)) :
    (SubexpNodeLiftData.nodeQuads p).get ⟨i.val, by rw [nodeQuads_length]; exact i.isLt⟩ =
      SubexpNodeLiftData.sourceQuad p (SubexpMachineNodeOrder.nodeCoefficients p i) := by
  simp [SubexpNodeLiftData.nodeQuads]

/-- The parser input is exactly the machine-generated node list, without
reordering or a second abstract enumeration. -/
theorem nodeQuads_flat_encoded :
    (SubexpNodeLiftData.nodeQuads p).map SubexpQuarticFlatMul.flat =
      SubexpMachineNodeOrder.nodeWords p := by
  have hf : (SubexpQuarticFlatMul.flat : Quad (Word (baseWidth p 1)) → List Bool) =
      SubexpNodeLiftData.encode := by
    funext a
    simp [SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
      FourWordPrograms.flatWords, SubexpNodeLiftData.encode, Quad.toFn, List.append_assoc]
  rw [hf]
  exact SubexpNodeLiftData.nodeQuads_encoded p

theorem power_inverse (exponent : List Bool) (hexp : BinaryArithmetic.toNat exponent = p^4 - 2)
    (a inverse : Quad (Word (baseWidth p 1)))
    (hv : PowerValue p 1 (QuarticSearch.liftedCoefficients p 1) exponent a inverse)
    (ha : fieldValue p a ≠ 0) :
    fieldValue p inverse = (fieldValue p a)⁻¹ := by
  have hpow : ringValue p inverse = ringValue p a ^ (p^4 - 2) := by
    change ringValue p inverse = ringValue p a ^ BinaryArithmetic.toNat exponent at hv
    simpa only [hexp] using hv
  have hi := SubexpFieldCacheAlgebra.source_power_inverse p
    (ringValue p a) (ringValue p inverse) hpow ha
  apply eq_inv_of_mul_eq_one_left
  simpa only [map_mul, map_one, fieldValue] using congrArg (rho p 1 (by decide)) hi

theorem inverseExponent_ne_zero : p^4 - 2 ≠ 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq : 16 ≤ p^4 := by
    calc
      16 = (2 : ℕ)^4 := by norm_num
      _ ≤ p^4 := Nat.pow_le_pow_left hp 4
  omega

theorem power_inverse_total (exponent : List Bool)
    (hexp : BinaryArithmetic.toNat exponent = p^4 - 2)
    (a inverse : Quad (Word (baseWidth p 1)))
    (hv : PowerValue p 1 (QuarticSearch.liftedCoefficients p 1) exponent a inverse) :
    fieldValue p inverse = (fieldValue p a)⁻¹ := by
  by_cases ha : fieldValue p a = 0
  · have hpow : ringValue p inverse = ringValue p a ^ (p^4 - 2) := by
      change ringValue p inverse = ringValue p a ^ BinaryArithmetic.toNat exponent at hv
      simpa only [hexp] using hv
    have hf : fieldValue p inverse = fieldValue p a ^ (p^4 - 2) := by
      simpa only [map_pow, fieldValue] using congrArg (rho p 1 (by decide)) hpow
    rw [ha, inv_zero]
    simpa only [ha, zero_pow (inverseExponent_ne_zero p)] using hf
  · exact power_inverse p exponent hexp a inverse hv ha

theorem negative_value (M : SubexpPreparedQuartic.Modulus p 1)
    (minusOne : Word (baseWidth p 1)) (hmone : wordValue p 1 minusOne = -1)
    (a : Quad (Word (baseWidth p 1))) :
    fieldValue p (SubexpQuarticNegMachine.negateWords p 1 M minusOne a) = -fieldValue p a := by
  have hneg : ringValue p (SubexpQuarticNegMachine.negateWords p 1 M minusOne a) =
      -ringValue p a := by
    change quotientDenote (QuarticSearch.liftedCoefficients p 1)
      ((SubexpQuarticNegMachine.negateWords p 1 M minusOne a).map (wordValue p 1)) =
        -quotientDenote (QuarticSearch.liftedCoefficients p 1) (a.map (wordValue p 1))
    exact SubexpQuarticNegMachine.negateWords_quotient p 1 M minusOne a hmone
      (QuarticSearch.liftedCoefficients p 1)
  simp only [fieldValue, hneg, map_neg]

theorem pair_inverse (M : SubexpPreparedQuartic.Modulus p 1)
    (minusOne : Word (baseWidth p 1)) (hmone : wordValue p 1 minusOne = -1)
    (exponent : List Bool) (hexp : BinaryArithmetic.toNat exponent = p^4 - 2)
    (a b inverse : Quad (Word (baseWidth p 1)))
    (hv : PairValue p 1 (QuarticSearch.liftedCoefficients p 1) exponent a
      (SubexpQuarticNegMachine.negateWords p 1 M minusOne b) inverse)
    (hne : fieldValue p a ≠ fieldValue p b) :
    fieldValue p inverse = (fieldValue p a - fieldValue p b)⁻¹ := by
  have hpow : ringValue p inverse = (ringValue p a - ringValue p b) ^ (p^4 - 2) := by
    change ringValue p inverse = (ringValue p a + ringValue p
      (SubexpQuarticNegMachine.negateWords p 1 M minusOne b)) ^
        BinaryArithmetic.toNat exponent at hv
    rw [show ringValue p (SubexpQuarticNegMachine.negateWords p 1 M minusOne b) =
      -ringValue p b by
        change quotientDenote (QuarticSearch.liftedCoefficients p 1)
          ((SubexpQuarticNegMachine.negateWords p 1 M minusOne b).map (wordValue p 1)) =
            -quotientDenote (QuarticSearch.liftedCoefficients p 1) (b.map (wordValue p 1))
        exact SubexpQuarticNegMachine.negateWords_quotient p 1 M minusOne b hmone
          (QuarticSearch.liftedCoefficients p 1),
      ← sub_eq_add_neg, hexp] at hv
    exact hv
  have hi := SubexpFieldCacheAlgebra.source_difference_inverse p
    (ringValue p a) (ringValue p b) (ringValue p inverse) hpow hne
  apply eq_inv_of_mul_eq_one_left
  simpa only [map_mul, map_sub, map_one, fieldValue] using
    congrArg (rho p 1 (by decide)) hi

theorem pair_inverse_total (M : SubexpPreparedQuartic.Modulus p 1)
    (minusOne : Word (baseWidth p 1)) (hmone : wordValue p 1 minusOne = -1)
    (exponent : List Bool) (hexp : BinaryArithmetic.toNat exponent = p^4 - 2)
    (a b inverse : Quad (Word (baseWidth p 1)))
    (hv : PairValue p 1 (QuarticSearch.liftedCoefficients p 1) exponent a
      (SubexpQuarticNegMachine.negateWords p 1 M minusOne b) inverse) :
    fieldValue p inverse = (fieldValue p a - fieldValue p b)⁻¹ := by
  by_cases heq : fieldValue p a = fieldValue p b
  · have hpow : ringValue p inverse = (ringValue p a - ringValue p b) ^ (p^4 - 2) := by
      change ringValue p inverse = (ringValue p a + ringValue p
        (SubexpQuarticNegMachine.negateWords p 1 M minusOne b)) ^
          BinaryArithmetic.toNat exponent at hv
      rw [show ringValue p (SubexpQuarticNegMachine.negateWords p 1 M minusOne b) =
        -ringValue p b by
          change quotientDenote (QuarticSearch.liftedCoefficients p 1)
            ((SubexpQuarticNegMachine.negateWords p 1 M minusOne b).map (wordValue p 1)) =
              -quotientDenote (QuarticSearch.liftedCoefficients p 1) (b.map (wordValue p 1))
          exact SubexpQuarticNegMachine.negateWords_quotient p 1 M minusOne b hmone
            (QuarticSearch.liftedCoefficients p 1),
        ← sub_eq_add_neg, hexp] at hv
      exact hv
    have hf : fieldValue p inverse = (fieldValue p a - fieldValue p b) ^ (p^4 - 2) := by
      simpa only [map_pow, map_sub, fieldValue] using congrArg (rho p 1 (by decide)) hpow
    rw [heq, sub_self, inv_zero]
    simpa only [heq, sub_self, zero_pow (inverseExponent_ne_zero p)] using hf
  · exact pair_inverse p M minusOne hmone exponent hexp a b inverse hv heq

/-- The same physical power routine produces zero on diagonal entries. -/
theorem pair_diagonal (M : SubexpPreparedQuartic.Modulus p 1)
    (minusOne : Word (baseWidth p 1)) (hmone : wordValue p 1 minusOne = -1)
    (exponent : List Bool) (hexp : BinaryArithmetic.toNat exponent = p^4 - 2)
    (a inverse : Quad (Word (baseWidth p 1)))
    (hv : PairValue p 1 (QuarticSearch.liftedCoefficients p 1) exponent a
      (SubexpQuarticNegMachine.negateWords p 1 M minusOne a) inverse) :
    fieldValue p inverse = 0 := by
  have hpow : ringValue p inverse = (ringValue p a - ringValue p a) ^ (p^4 - 2) := by
    change ringValue p inverse = (ringValue p a + ringValue p
      (SubexpQuarticNegMachine.negateWords p 1 M minusOne a)) ^
        BinaryArithmetic.toNat exponent at hv
    rw [show ringValue p (SubexpQuarticNegMachine.negateWords p 1 M minusOne a) =
      -ringValue p a by
        change quotientDenote (QuarticSearch.liftedCoefficients p 1)
          ((SubexpQuarticNegMachine.negateWords p 1 M minusOne a).map (wordValue p 1)) =
            -quotientDenote (QuarticSearch.liftedCoefficients p 1) (a.map (wordValue p 1))
        exact SubexpQuarticNegMachine.negateWords_quotient p 1 M minusOne a hmone
          (QuarticSearch.liftedCoefficients p 1),
      ← sub_eq_add_neg, hexp] at hv
    exact hv
  rw [sub_self, SubexpFieldCacheAlgebra.source_zero_power] at hpow
  simp only [fieldValue, hpow, map_zero]

/-- An index theorem for the inverse array in the exact generator order. -/
theorem node_inverse_get (exponent : List Bool)
    (hexp : BinaryArithmetic.toNat exponent = p^4 - 2)
    (ys : List (Quad (Word (baseWidth p 1))))
    (hys : List.Forall₂ (PowerValue p 1 (QuarticSearch.liftedCoefficients p 1) exponent)
      (SubexpNodeLiftData.nodeQuads p) ys) (i : Fin (p^4 - 1)) :
    fieldValue p (ys.get ⟨i.val, by rw [← hys.length_eq, nodeQuads_length]; exact i.isLt⟩) =
      ((SubexpMachineNodeOrder.nodeEquiv p i).val)⁻¹ := by
  have hv := hys.get (by rw [nodeQuads_length]; exact i.isLt)
    (by rw [← hys.length_eq, nodeQuads_length]; exact i.isLt)
  rw [nodeQuads_get p i] at hv
  have hn := node_value p i
  have hi := power_inverse p exponent hexp _ _ hv
    (by rw [hn]; exact (SubexpMachineNodeOrder.nodeEquiv p i).property)
  simpa only [hn] using hi

theorem negativeWords_get (M : SubexpPreparedQuartic.Modulus p 1)
    (minusOne : Word (baseWidth p 1)) (j : Fin (p^4 - 1)) :
    (negativeWords p 1 M minusOne (SubexpNodeLiftData.nodeQuads p)).get
      ⟨j.val, by simp [negativeWords, nodeQuads_length]⟩ =
    SubexpQuarticNegMachine.negateWords p 1 M minusOne
      (SubexpNodeLiftData.sourceQuad p (SubexpMachineNodeOrder.nodeCoefficients p j)) := by
  simp [negativeWords, SubexpNodeLiftData.nodeQuads]

/-- Every off-diagonal entry denotes the required inverse difference, with
the positive-node index first and negative-node index second. -/
theorem pair_inverse_get (M : SubexpPreparedQuartic.Modulus p 1)
    (minusOne : Word (baseWidth p 1)) (hmone : wordValue p 1 minusOne = -1)
    (exponent : List Bool) (hexp : BinaryArithmetic.toNat exponent = p^4 - 2)
    (rows : List (List (Quad (Word (baseWidth p 1)))))
    (hrows : List.Forall₂ (fun node row => List.Forall₂
      (PairValue p 1 (QuarticSearch.liftedCoefficients p 1) exponent node)
      (negativeWords p 1 M minusOne (SubexpNodeLiftData.nodeQuads p)) row)
      (SubexpNodeLiftData.nodeQuads p) rows)
    (i j : Fin (p^4 - 1)) (hij : i ≠ j)
    (hi : i.val < rows.length)
    (hj : j.val < (rows.get ⟨i.val, hi⟩).length) :
    fieldValue p ((rows.get ⟨i.val, hi⟩).get ⟨j.val, hj⟩) =
      ((SubexpMachineNodeOrder.nodeEquiv p i).val -
        (SubexpMachineNodeOrder.nodeEquiv p j).val)⁻¹ := by
  have hrow := hrows.get (by rw [nodeQuads_length]; exact i.isLt) hi
  rw [nodeQuads_get p i] at hrow
  have hentry := hrow.get (by simp [negativeWords, nodeQuads_length]) hj
  rw [negativeWords_get p M minusOne j] at hentry
  have hne : fieldValue p (SubexpNodeLiftData.sourceQuad p
      (SubexpMachineNodeOrder.nodeCoefficients p i)) ≠
      fieldValue p (SubexpNodeLiftData.sourceQuad p
        (SubexpMachineNodeOrder.nodeCoefficients p j)) := by
    rw [node_value, node_value]
    intro he
    exact hij ((SubexpMachineNodeOrder.nodeEquiv p).injective (Subtype.ext he))
  have hv := pair_inverse p M minusOne hmone exponent hexp _ _ _ hentry hne
  simpa only [node_value] using hv

open BitProgram StructuredCalls SubexpCRTCofactorControl

/-- End-to-end execution on the exact framed node list produced by the field
setup machine. The two inverse arrays have their selected-field meanings,
including zero on the diagonal, and the source-node output is unframed. -/
theorem selected_program_run (M : SubexpPreparedQuartic.Modulus p 1)
    (t unit : Quad (Word (baseWidth p 1))) (minusOne : Word (baseWidth p 1))
    (ht : t.map (wordValue p 1) = reductionData (QuarticSearch.liftedCoefficients p 1))
    (hu : quotientDenote (QuarticSearch.liftedCoefficients p 1)
      (unit.map (wordValue p 1)) = 1)
    (hminus : wordValue p 1 minusOne = -1)
    (base : Words) (hm : base.modulus = M.bits)
    (hr : base.reduction = SubexpQuarticFlatMul.flat t)
    (hone : base.unit = SubexpQuarticFlatMul.flat unit)
    (hmone : base.minusOne = minusOne.val) (hw : base.width.length = baseWidth p 1)
    (hblock : base.blockWidth = [])
    (hexp : BinaryArithmetic.toNat base.exponent = p^4 - 2)
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (hsource : frame 97 = ProgramEncoding.encodeRecords (SubexpMachineNodeOrder.nodeWords p))
    (hnegative : frame 100 = []) (hdifference : frame 103 = []) (houter : frame 106 = []) :
    ∃ rf ys rows,
      List.Forall₂ (fun a b => fieldValue p b = (fieldValue p a)⁻¹)
        (SubexpNodeLiftData.nodeQuads p) ys ∧
      List.Forall₂ (fun a row => List.Forall₂
        (fun b inverse => fieldValue p inverse = (fieldValue p a - fieldValue p b)⁻¹)
        (SubexpNodeLiftData.nodeQuads p) row) (SubexpNodeLiftData.nodeQuads p) rows ∧
      RunsIn SubexpFieldCacheMachine.program
        (SubexpFieldCacheProgram.budget (baseWidth p 1) base.exponent (p^4 - 1) + 1)
        ((state regs frame (SubexpFieldCacheNodeLoop.ready base [] [])).withPC
          (some SubexpFieldCacheMachine.program.entry))
        ((state rf (SubexpFieldCacheProgram.resultFrame frame
          (SubexpMachineNodeOrder.nodeWords p).flatten
          (SubexpFieldCacheNodeLoop.negativeBytes p 1 M minusOne (SubexpNodeLiftData.nodeQuads p))
          (rows.flatten.flatMap SubexpQuarticFlatMul.flat))
          (SubexpFieldCacheNodeLoop.ready base [] (ys.flatMap SubexpQuarticFlatMul.flat))).withPC none) := by
  have hB : 0 < baseWidth p 1 := Nat.mul_pos (by decide) (Nat.succ_pos _)
  have hsrc : frame 97 = ProgramEncoding.encodeRecords
      ((SubexpNodeLiftData.nodeQuads p).map SubexpQuarticFlatMul.flat) := by
    simpa only [nodeQuads_flat_encoded] using hsource
  obtain ⟨rf, ys, rows, hys, hrows, he⟩ := SubexpFieldCacheProgram.program_value
    p 1 M (QuarticSearch.liftedCoefficients p 1) t unit minusOne ht hu
    base hm hr hone hmone hw hblock hB (SubexpNodeLiftData.nodeQuads p) regs frame
    hsrc hnegative hdifference houter
  have hysValue := List.Forall₂.imp
    (fun a b hab => power_inverse_total p base.exponent hexp a b hab) hys
  have hrowsValue : List.Forall₂ (fun a row => List.Forall₂
      (fun b inverse => fieldValue p inverse = (fieldValue p a - fieldValue p b)⁻¹)
      (SubexpNodeLiftData.nodeQuads p) row) (SubexpNodeLiftData.nodeQuads p) rows := by
    apply List.Forall₂.imp ?_ hrows
    intro a row hrow
    have hrow' : List.Forall₂ (fun b inverse =>
        PairValue p 1 (QuarticSearch.liftedCoefficients p 1) base.exponent a
          (SubexpQuarticNegMachine.negateWords p 1 M minusOne b) inverse)
        (SubexpNodeLiftData.nodeQuads p) row := by
      simpa only [negativeWords, List.forall₂_map_left_iff] using hrow
    exact List.Forall₂.imp
      (fun b inverse hbi => pair_inverse_total p M minusOne hminus base.exponent hexp a b inverse hbi)
      hrow'
  have hflat : (SubexpNodeLiftData.nodeQuads p).flatMap SubexpQuarticFlatMul.flat =
      (SubexpMachineNodeOrder.nodeWords p).flatten := by
    rw [List.flatMap_def, nodeQuads_flat_encoded]
  refine ⟨rf, ys, rows, hysValue, hrowsValue, ?_⟩
  simpa only [nodeQuads_length, hflat] using he

end SubexponentialSAT.SubexpFieldCacheInterpretation

end OAI.Algorithms
