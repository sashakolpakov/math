import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterExecution
import OAI.Algorithms.SubexponentialSAT.SubexpCRTSelectedInput
import OAI.Algorithms.SubexponentialSAT.SubexpH0CountDecision

namespace OAI.Algorithms

/-! The concrete CRT program on the selected lifted ring and the represented
node/jet arrays. All residue-field, nilpotence and inverse premises are
proved here from the selected construction. -/

namespace SubexponentialSAT.SubexpCRTOuterSelected

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

/-- The scalar output is exactly the singleton-polynomial byte format read
by the existing count decoder. -/
theorem encode_singleton {B : ℕ} (a : Quad (Word B)) :
    SubexpFlatAdd.encode a = SubexpFlatCount.flatPolynomial [a] := by
  simp [SubexpFlatAdd.encode, SubexpFlatAdd.quadWords, SubexpFlatAdd.flatten,
    SubexpFlatCount.flatPolynomial, SubexpFlatCount.flatCoefficient]

variable {p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (S : Factor.System V F (ZMod p)) {c : SubexpLayoutSpec.Parameters p k Δ r tau}
  (L : SubexpLayoutSpec.Layout (E := SubexpActualRing.E p) S.toPattern c)

local notation "D" => Fintype.card V
local notation "B" => baseWidth p (D + 1)
local notation "coeffs" => QuarticSearch.liftedCoefficients p (D + 1)

omit [DecidableEq F] in
/-- The represented inputs identify the actual producer's node and jet
values. Neither the desired count nor the CRT output is a premise. -/
theorem program_value (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t one : SubexpCRTSelectedInput.Coefficient p D)
    (minusOne : Word B) (width exponent : List Bool)
    (nodes : Fin c.Q → SubexpCRTSelectedInput.Coefficient p D)
    (jets : Fin c.Q → SubexpCRTSelectedInput.Jet p D)
    (hD : 0 < D) (hw : width.length = B)
    (ht : t.map (wordValue p (D + 1)) = reductionData coeffs)
    (ho : SubexpCRTSelectedInput.decode p D one = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    (hexponent : BinaryArithmetic.toNat exponent = p^4 - 2)
    (hnodes : ∀ i, SubexpCRTSelectedInput.decode p D (nodes i) = SubexpCRTAtZero.selectedNode S L i)
    (hjets : ∀ i, SubexpCRTSelectedInput.denote p D (jets i) = SubexpCRTSelectedInput.selectedJet S L i)
    (regs : Fin 16 → Bool) :
    ∃ (out : SubexpCRTOuterProgram.Data) (b : SubexpCRTSelectedInput.Coefficient p D),
      RunsIn SubexpCRTOuterProgram.program
        (SubexpCRTOuterExecution.commandBudget p D c.Q exponent + 1)
        ((SubexpCRTOuterInput.data p D M t one minusOne width exponent nodes jets regs).withPC
          (some SubexpCRTOuterProgram.program.entry)) (out.withPC none) ∧
      out.stacks 261 = SubexpFlatAdd.encode b ∧
      SubexpHornerMachine.decode p (D + 1) coeffs b = SubexpCRTAtZero.selectedValue S L := by
  let rho := SubexpActualRing.rho p (D + 1) (Nat.succ_pos D)
  have hres (i : Fin c.Q) : rho (SubexpCRTSelectedInput.decode p D (nodes i)) = L.node i := by
    rw [hnodes i]
    exact (SubexpCounting.selectedLiftedLayout S L (D + 1) (Nat.succ_pos D)).residue_theta i
  have hinj : Function.Injective (fun i => rho (SubexpCRTSelectedInput.decode p D (nodes i))) := by
    intro i j hij
    apply SubexpLayoutSpec.Layout.node_injective L
    simpa only [hres] using hij
  let z := SubexpHornerMachine.zeroCode p (D + 1)
  have hzcode : SubexpFlatAdd.encode z = List.replicate (4 * B) false := by
    rw [← SubexpHornerMachine.flat_eq_encode]
    exact SubexpHornerMachine.zeroCode_flat p (D + 1)
  have hz : SubexpCRTOuterExecution.decode p D coeffs z = 0 :=
    SubexpHornerMachine.zeroCode_decode p (D + 1) coeffs
  have ha := SubexpCRTSelectedInput.selectedInverse_correct_of_nodes S L nodes hnodes
  obtain ⟨out, b, hr, hout, hv⟩ := SubexpCRTOuterExecution.program_value p D M t z one
    minusOne width exponent nodes jets hw hzcode hD coeffs ht hz ho hminus
    rho (p^4) (SubexpActualRing.extension_card p)
    (p : SubexpActualRing.Ring p (D + 1)) (SubexpActualRing.prime_power_zero p (D + 1))
    (fun x hx => (SubexpActualRing.rho_eq_zero_iff p (D + 1) (Nat.succ_pos D) x).mp hx)
    hinj hexponent (SubexpCRTSelectedInput.selectedInverse S L) ha regs
  exact ⟨out, b, hr, hout, SubexpCRTSelectedInput.output_value_eq_selected S L nodes jets
    (SubexpCRTSelectedInput.selectedInverse S L) hnodes hjets ha b hv⟩

omit [DecidableEq F] in
/-- The first word of the actual returned quartet carries the exact count
modulo the prepared modulus. The decoder proves the corresponding SAT test. -/
theorem program_count (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t one : SubexpCRTSelectedInput.Coefficient p D)
    (minusOne : Word B) (width exponent : List Bool)
    (nodes : Fin c.Q → SubexpCRTSelectedInput.Coefficient p D)
    (jets : Fin c.Q → SubexpCRTSelectedInput.Jet p D)
    (hD : 0 < D) (hw : width.length = B)
    (ht : t.map (wordValue p (D + 1)) = reductionData coeffs)
    (ho : SubexpCRTSelectedInput.decode p D one = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    (hexponent : BinaryArithmetic.toNat exponent = p^4 - 2)
    (hnodes : ∀ i, SubexpCRTSelectedInput.decode p D (nodes i) = SubexpCRTAtZero.selectedNode S L i)
    (hjets : ∀ i, SubexpCRTSelectedInput.denote p D (jets i) = SubexpCRTSelectedInput.selectedJet S L i)
    (regs : Fin 16 → Bool) :
    ∃ (out : SubexpCRTOuterProgram.Data) (b : SubexpCRTSelectedInput.Coefficient p D),
      RunsIn SubexpCRTOuterProgram.program
        (SubexpCRTOuterExecution.commandBudget p D c.Q exponent + 1)
        ((SubexpCRTOuterInput.data p D M t one minusOne width exponent nodes jets regs).withPC
          (some SubexpCRTOuterProgram.program.entry)) (out.withPC none) ∧
      out.stacks 261 = SubexpFlatAdd.encode b ∧
      BinaryArithmetic.toNat b.c0.val % p^(D + 1) = Factor.count S := by
  obtain ⟨out, b, hr, hout, hv⟩ := program_value S L M t one minusOne width exponent nodes jets
    hD hw ht ho hminus hexponent hnodes hjets regs
  exact ⟨out, b, hr, hout, SubexpH0CountDecision.firstWord_mod S L b hD hv⟩

end SubexponentialSAT.SubexpCRTOuterSelected

end OAI.Algorithms
