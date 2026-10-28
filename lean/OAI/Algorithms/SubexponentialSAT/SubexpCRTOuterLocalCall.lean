import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterInput
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCanonicalInput

namespace OAI.Algorithms

/-! Relocation of the actual local CRT correction program into the outer
controller. The canonical input is constructed from represented words; the
correction polynomial comes from the finite program's proved execution. -/

namespace SubexponentialSAT.SubexpCRTOuterLocalCall

attribute [local simp] Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpPolynomialPowerProgram
open SubexpCRTOuterProgram (Code Data localPorts)

def command : Code :=
  .call (ProgramLinking.liftProgram SubexpLocalCRTProgram.program id localPorts)

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D

def budget (Q : ℕ) (exponent : List Bool) : ℕ :=
  SubexpQuarticPowerProgram.runtimeBound (baseWidth p (D + 1)) exponent +
    5000000 * (Q + 1) * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2 + 3

theorem command_eval {Q : ℕ} (t z one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width exponent : List Bool)
    (nodes : Fin Q → Coeff p D) (i : Fin Q) (index : List Bool) (J : Poly p D)
    (hw : width.length = baseWidth p (D + 1))
    (hzcode : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p (D + 1)) false)
    (hindex : index.length = i.val) (hD : 0 < D)
    (c : Fin 4 → ZMod (p^(D + 1)))
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : SubexpLocalValueCorrectness.decode p D c z = 0)
    (ho : SubexpLocalValueCorrectness.decode p D c one = 1)
    (hminus : wordValue p (D + 1) minusOne = -1)
    {E : Type*} [Field E] [Fintype E]
    (ρ : SubexpLocalValueCorrectness.Ring p D c →+* E)
    (q : ℕ) (hq : Fintype.card E = q)
    (π : SubexpLocalValueCorrectness.Ring p D c) (hπ : π^(D + 1) = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hnodes : Function.Injective (fun j => ρ (SubexpLocalValueCorrectness.decode p D c (nodes j))))
    (hexponent : BinaryArithmetic.toNat exponent = q - 2)
    (a : SubexpLocalValueCorrectness.Ring p D c)
    (ha : a * (TruncatedInverse.localFactor
      (fun j => SubexpLocalValueCorrectness.decode p D c (nodes j)) D i).coeff 0 = 1)
    (d : Data)
    (hstore : ∀ j, d.stacks (localPorts j) =
      SubexpCRTCanonicalInput.canonical p D M t (nodes i) one minusOne width exponent
        (List.ofFn nodes) index J j) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool) (W : Poly p D), n ≤ budget p D Q exponent ∧
      Eval command n d ⟨rf, Function.update d.stacks 244 (encode p (D + 1) W)⟩ ∧
      SubexpLocalValueCorrectness.denote p D c W =
        TruncatedInverse.correctedJet
          (TruncatedInverse.localFactor (fun j => SubexpLocalValueCorrectness.decode p D c (nodes j)) D i)
          (SubexpLocalValueCorrectness.denote p D c J) a D := by
  let s := SubexpCRTCanonicalInput.canonical p D M t (nodes i) one minusOne width exponent
    (List.ofFn nodes) index J
  have hinput := SubexpCRTCanonicalInput.input p D M t (nodes i) one minusOne width exponent
    (List.ofFn nodes) index J z hw hzcode
  let property : Poly p D → Prop := fun W => SubexpLocalValueCorrectness.denote p D c W =
    TruncatedInverse.correctedJet
      (TruncatedInverse.localFactor (fun j => SubexpLocalValueCorrectness.decode p D c (nodes j)) D i)
      (SubexpLocalValueCorrectness.denote p D c J) a D
  let K := SubexpQuarticPowerProgram.runtimeBound (baseWidth p (D + 1)) exponent +
    5000000 * (Q + 1) * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2
  have hpositive : ∀ regs : Fin 16 → Bool, ∃ (n : ℕ) (regs' : Fin 16 → Bool) (W : Poly p D), n ≤ K ∧
      Eval SubexpLocalCRTProgram.positiveDimension n ⟨regs, s⟩
        ⟨regs', Function.update s 244 (encode p (D + 1) W)⟩ ∧ property W := by
    intro regs
    have he : BinaryArithmetic.toNat (s 206) = q - 2 := by
      simpa [s, SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
        SubexpCRTCanonicalInput.context] using hexponent
    have h := SubexpLocalCRTExecution.positive_correct p D M s t z one minusOne width (fun _ => [])
      nodes i index J hinput hindex hD c ht hz ho hminus ρ q hq π hπ hker hnodes he a ha regs
    simpa [K, s, SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
      SubexpCRTCanonicalInput.context] using h
  have hdlen : 0 < (s 243).length := by
    simpa [s, SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store,
      SubexpCRTCanonicalInput.context] using hD
  obtain ⟨n, rf, W, hn, he, hvalue⟩ :=
    SubexpLocalCRTExecution.command_of_positive p D s K property hdlen hpositive d.regs
  have hp : projectState id localPorts d = (⟨d.regs, s⟩ : State 16 256) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j
      exact hstore j
  have htrace := SubexpLocalCRTExecution.program_trace he
  have hcall := eval_call_from_state SubexpLocalCRTProgram.program id localPorts d
    Function.injective_id localPorts.injective
    (b := ⟨rf, Function.update s 244 (encode p (D + 1) W)⟩)
    (by simpa only [hp] using htrace)
  have hagree : Function.extend localPorts s d.stacks = d.stacks :=
    SubexpQuarticFlatLift.extend_agree localPorts s d.stacks hstore
  have hfinal : embedState id localPorts d
      (⟨rf, Function.update s 244 (encode p (D + 1) W)⟩ : State 16 256) =
      (⟨rf, Function.update d.stacks 244 (encode p (D + 1) W)⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · exact ProgramLinking.extend_id _ _
    · change Function.extend localPorts (Function.update s 244 _) d.stacks = _
      rw [ProgramLinking.extend_update localPorts.injective, hagree]
      rfl
  refine ⟨n + 1, rf, W, ?_, ?_, hvalue⟩
  · unfold budget
    dsimp [K] at hn
    omega
  · simpa only [command, hfinal] using hcall

end SubexponentialSAT.SubexpCRTOuterLocalCall

end OAI.Algorithms
