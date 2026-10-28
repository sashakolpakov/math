import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalGeometricProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalProductScan
import OAI.Algorithms.SubexponentialSAT.SubexpLocalProductAlgebra
import OAI.Algorithms.SubexponentialSAT.SubexpLocalSeriesCorrectness

namespace OAI.Algorithms

/-! Semantic refinement of the exact coefficient lists returned by the
local CRT programs. The executable operations are the concrete prepared
quartic programs, while the target is the established general-ring CRT. -/

namespace SubexponentialSAT.SubexpLocalValueCorrectness

open Polynomial SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))
variable (c : Fin 4 → ZMod (p^(D + 1)))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D
abbrev Ring := LiftRing.Extension (QuarticSearch.poly c)

noncomputable def decode (a : Coeff p D) : Ring p D c :=
  quotientDenote c (a.map (wordValue p (D + 1)))

noncomputable def denote (P : Poly p D) : (Ring p D c)[X] :=
  PolynomialAlgorithm.denote (P.val.map (decode p D c))

def constant (z a : Coeff p D) : Poly p D :=
  ⟨SubexpLocalCorrectionAlgebra.padded z a z D,
    SubexpLocalCorrectionAlgebra.padded_length _ _ _ _⟩

def zero (z : Coeff p D) : Poly p D :=
  ⟨List.replicate D z, List.length_replicate⟩

omit [Fact p.Prime] in
theorem constant_denote (z a : Coeff p D) (hz : decode p D c z = 0) :
    denote p D c (constant p D z a) = Truncation.trunc D (C (decode p D c a)) := by
  unfold denote constant
  rw [SubexpLocalCorrectionAlgebra.padded_denote (decode p D c) z a z hz D]
  simp [hz]

omit [Fact p.Prime] in
theorem zero_denote (z : Coeff p D) (hz : decode p D c z = 0) :
    denote p D c (zero p D z) = 0 := by
  simp [denote, zero, hz, SubexpConvolutionAlgebra.denote_replicate_zero]

theorem next_denote (t z : Coeff p D)
    (ht : t.map (wordValue p (D + 1)) = reductionData c) (hz : decode p D c z = 0)
    (Q P : Poly p D) :
    denote p D c (next p (D + 1) M t z Q P) =
      Truncation.trunc D (denote p D c P * denote p D c Q) :=
  SubexpTruncatedMultiply.result_correct p (D + 1) M c t z ht hz D P.val Q.val

theorem sum_denote (t z o : Coeff p D)
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : decode p D c z = 0) (ho : decode p D c o = 1) (P Q : Poly p D) :
    denote p D c (SubexpPolynomialHornerProgram.sum p D M t z o P Q) =
      denote p D c P + denote p D c Q := by
  let ops := SubexpSymbolicCost.preparedRing p D M c t z o ht hz ho
  change PolynomialAlgorithm.denote
    (SubexpDensePolynomial.decodeList ops (SubexpDensePolynomial.addProgram ops.program P.val Q.val).1) = _
  rw [SubexpDensePolynomial.addProgram_run, SubexpDensePolynomial.addRun_correct,
    PolynomialAlgorithm.denote_add]
  rfl

theorem nodeScan_denote (t z o theta : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : decode p D c z = 0) (ho : decode p D c o = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    (nodes : List (Coeff p D)) (index : List Bool) :
    denote p D c (SubexpNodeScanControl.run
      (SubexpLocalProductScan.stepValue p D M t z theta o minusOne)
      nodes ⟨constant p D z o, index, true⟩).value =
        Truncation.trunc D (((nodes.eraseIdx index.length).map
          (fun x => (X + C (decode p D c theta - decode p D c x))^D)).prod) := by
  have h := SubexpLocalProductAlgebra.scan_denote D (denote p D c)
    (fun P Q => next p (D + 1) M t z Q P)
    (fun P Q => next_denote p D M c t z ht hz Q P)
    (fun x => SubexpLocalProductProgram.factor p (D + 1) M minusOne z theta x o D)
    (fun x => X + C (decode p D c theta - decode p D c x))
    (fun x => SubexpLocalLinearFactorProgram.factor_denote p (D + 1) M c
      minusOne hminus z theta x o hz ho D)
    nodes index (constant p D z o) 1 (by
      rw [constant_denote p D c z o hz, ho, map_one])
  have hstep : SubexpLocalProductScan.stepValue p D M t z theta o minusOne =
      fun P x => ((fun y => next p (D + 1) M t z
        (SubexpLocalProductProgram.factor p (D + 1) M minusOne z theta x o D) y)^[D]) P :=
    rfl
  rw [hstep]
  simpa only [one_mul] using h

theorem nodeScan_localFactor (t z o : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : decode p D c z = 0) (ho : decode p D c o = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    {Q : ℕ} (nodes : Fin Q → Coeff p D) (i : Fin Q)
    (index : List Bool) (hindex : index.length = i.val) :
    denote p D c (SubexpNodeScanControl.run
      (SubexpLocalProductScan.stepValue p D M t z (nodes i) o minusOne)
      (List.ofFn nodes) ⟨constant p D z o, index, true⟩).value =
        Truncation.trunc D (TruncatedInverse.localFactor (fun j => decode p D c (nodes j)) D i) := by
  rw [nodeScan_denote p D M c t z o (nodes i) minusOne ht hz ho hminus, hindex]
  congr 1
  have h := SubexpLocalProductAlgebra.product_excluding_node
    (fun j => decode p D c (nodes j)) D i
  have hof : List.ofFn (fun j => decode p D c (nodes j)) =
      (List.ofFn nodes).map (decode p D c) := by rw [List.map_ofFn]; rfl
  rw [hof, List.eraseIdx_map, List.map_map] at h
  exact h

theorem defect_denote (t z o seed : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : decode p D c z = 0) (ho : decode p D c o = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    (Pt : Poly p D) (P : (Ring p D c)[X])
    (hPt : denote p D c Pt = Truncation.trunc D P) :
    denote p D c (SubexpLocalGeometricProgram.defect p D M t z o Pt
      (constant p D z (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne seed))
      (constant p D z o)) =
        Truncation.trunc D (1 - C (decode p D c seed) * P) := by
  apply SubexpLocalSeriesCorrectness.defect_denote D Pt _ _
    (SubexpPolynomialHornerProgram.sum p D M t z o)
    (fun P Q => next p (D + 1) M t z Q P) (denote p D c) P (decode p D c seed) hPt
  · rw [constant_denote p D c z _ hz]
    congr 2
    exact SubexpQuarticNegMachine.negateWords_quotient p (D + 1) M minusOne seed hminus c
  · rw [constant_denote p D c z o hz, ho, map_one]
  · exact sum_denote p D M c t z o ht hz ho
  · intro P Q
    exact next_denote p D M c t z ht hz Q P

theorem correction_denote (t z o seed : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : decode p D c z = 0) (ho : decode p D c o = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    (Pt J : Poly p D) (P : (Ring p D c)[X]) (a : Ring p D c)
    (hPt : denote p D c Pt = Truncation.trunc D P)
    (ha : a * P.coeff 0 = 1)
    (hseed : (1 - decode p D c seed * P.coeff 0)^(D + 1) = 0) :
    let O := constant p D z o
    let Cb := constant p D z seed
    let N := constant p D z (SubexpLocalLinearFactorProgram.negative p (D + 1) M minusOne seed)
    let F := SubexpLocalGeometricProgram.defect p D M t z o Pt N O
    let I := SubexpLocalGeometricProgram.inverseValue p D M t z o F O (zero p D z) Cb
    denote p D c (next p (D + 1) M t z J I) =
      TruncatedInverse.correctedJet P (denote p D c J) a D := by
  dsimp only
  apply SubexpLocalSeriesCorrectness.correction_denote D (D + 1) (zero p D z)
    (constant p D z o) _ (constant p D z seed) J
    (SubexpPolynomialHornerProgram.sum p D M t z o)
    (fun P Q => next p (D + 1) M t z Q P) (denote p D c)
    P (denote p D c J) a (decode p D c seed)
  · exact zero_denote p D c z hz
  · rw [constant_denote p D c z o hz, ho, map_one]
  · exact defect_denote p D M c t z o seed minusOne ht hz ho hminus Pt P hPt
  · exact constant_denote p D c z seed hz
  · rfl
  · exact sum_denote p D M c t z o ht hz ho
  · intro P Q
    exact next_denote p D M c t z ht hz Q P
  · exact ha
  · exact hseed

end SubexponentialSAT.SubexpLocalValueCorrectness

end OAI.Algorithms
