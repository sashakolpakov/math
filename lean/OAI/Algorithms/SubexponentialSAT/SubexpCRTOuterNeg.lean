import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterSetup
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatNeg

namespace OAI.Algorithms

/-! The outer CRT negates its current point using the actual flat quartet
service. The original point and arithmetic metadata are preserved; the only
changed stack at the complete boundary is output 263. -/

namespace SubexponentialSAT.SubexpCRTOuterNeg

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing SubexpCRTOuterProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def ports : Fin 24 ↪ Fin 320 :=
  ⟨![20,21,22,23,211,25,26,27,28,29,30,31,32,33,5,35,36,37,218,219,10,41,42,43],
    by decide⟩

@[simp] theorem ports_input : ports 18 = 218 := rfl
@[simp] theorem ports_output : ports 19 = 219 := rfl

def scalarNegate : Code := SubexpQuarticFlatNeg.callAt registers ports

def command : Code := .seq (copy 259 218)
  (.seq scalarNegate (.seq (move 219 263) (clear 218)))

abbrev program : Program 16 320 (size command + 1) := compiled command 259 263

def blankStore (minusOne modulus width : List Bool) : Fin 24 → List Bool :=
  SubexpQuarticFlatNeg.bankStore (SubexpQuarticFlatNeg.emptyBank minusOne)
    modulus [] width []

def runtimeBound (B : ℕ) : ℕ := 25000 * (B + 1)^2 + 60 * B + 14

theorem initialStore_update {B : ℕ} (a : Quad (Word B)) (minusOne : Word B)
    (modulus width : List Bool) :
    SubexpQuarticFlatNeg.initialStore a minusOne modulus width =
      Function.update (blankStore minusOne.val modulus width) 18
        (SubexpQuarticFlatNeg.flat a) := by
  funext i
  by_cases hi : i = 18
  · subst i
    simp [SubexpQuarticFlatNeg.initialStore,blankStore,SubexpQuarticFlatNeg.bankStore]
  · simp [SubexpQuarticFlatNeg.initialStore,blankStore,SubexpQuarticFlatNeg.bankStore,hi]

theorem ready_after_copy {B : ℕ} (a : Quad (Word B)) (minusOne : Word B)
    (modulus width : List Bool) (s : Fin 320 → List Bool)
    (hs : ∀ i, s (ports i) = blankStore minusOne.val modulus width i) :
    ∀ i, Function.update s 218 (SubexpQuarticFlatNeg.flat a) (ports i) =
      SubexpQuarticFlatNeg.initialStore a minusOne modulus width i := by
  intro i
  rw [initialStore_update]
  change Function.update s (ports 18) (SubexpQuarticFlatNeg.flat a) (ports i) = _
  simp only [Function.update_apply,ports.injective.eq_iff,hs]

theorem command_eval (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (width : List Bool) (hw : width.length = baseWidth p μ) (d : Data)
    (hcurrent : d.stacks 259 = SubexpQuarticFlatNeg.flat a)
    (hservice : ∀ i, d.stacks (ports i) = blankStore minusOne.val M.bits width i)
    (h263 : d.stacks 263 = []) (h318 : d.stacks 318 = []) (h319 : d.stacks 319 = []) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ runtimeBound (baseWidth p μ) ∧
      Eval command n d
        ⟨rf, Function.update d.stacks 263 (SubexpQuarticFlatNeg.flat
          (SubexpQuarticNegMachine.negateWords p μ M minusOne a))⟩ := by
  let B := baseWidth p μ
  let negative := SubexpQuarticNegMachine.negateWords p μ M minusOne a
  have h218 : d.stacks 218 = [] := by
    simpa [blankStore,SubexpQuarticFlatNeg.bankStore] using hservice 18
  have h219 : d.stacks 219 = [] := by
    simpa [blankStore,SubexpQuarticFlatNeg.bankStore] using hservice 19
  let d₁ : Data := ⟨readRegs d.regs 0 1 none,
    Function.update d.stacks 218 (SubexpQuarticFlatNeg.flat a)⟩
  have hc : Eval (copy 259 218) (28 * B + 5) d d₁ := by
    have h := copy_run d 259 218 (by decide) (by decide) (by decide) h318
    simpa [afterCopy,StackRoutines.copyStacks,d₁,hcurrent,h218,
      SubexpQuarticFlatNeg.flat_length,B,← Nat.mul_assoc] using h
  obtain ⟨n, rf, hn, he⟩ := SubexpQuarticFlatNeg.callAt_eval registers ports
    p μ M a minusOne width hw d₁ (ready_after_copy a minusOne M.bits width d.stacks hservice)
  let d₂ : Data := ⟨Function.extend registers rf d₁.regs,
    Function.update d₁.stacks 219 (SubexpQuarticFlatNeg.flat negative)⟩
  have he' : Eval scalarNegate n d₁ d₂ := by
    simpa only [scalarNegate,ports_output,d₂,negative] using he
  let d₃ := moved d₂ 219 263
  have hm : Eval (move 219 263) (24 * B + 6) d₂ d₃ := by
    have h := move_run d₂ 219 263 (by decide) (by decide) (by decide)
      (by simp [d₂,d₁,h319]) (by simp [d₂,d₁,h263])
    simpa [d₂,d₃,SubexpQuarticFlatNeg.flat_length,B,← Nat.mul_assoc] using h
  let d₄ := SubexpSetupStorage.clearState 218 d₃
  have hz : Eval (clear 218) (8 * B + 3) d₃ d₄ := by
    have h := clear_run d₃ 218
    simpa [d₄,d₃,moved,d₂,d₁,SubexpQuarticFlatNeg.flat_length,B,← Nat.mul_assoc] using h
  have hout : d₄.stacks = Function.update d.stacks 263 (SubexpQuarticFlatNeg.flat negative) := by
    funext j
    by_cases h218' : j = 218
    · subst j
      simp [d₄,SubexpSetupStorage.clearState,d₃,d₂,d₁,h218]
    · by_cases h219' : j = 219
      · subst j
        simp [d₄,SubexpSetupStorage.clearState,d₃,d₂,d₁,h219]
      · by_cases h263' : j = 263
        · subst j
          simp [d₄,SubexpSetupStorage.clearState,d₃,d₂,d₁]
        · simp [d₄,SubexpSetupStorage.clearState,d₃,d₂,d₁,
            h218',h219',h263']
  have hfinal : d₄ = (⟨d₄.regs, Function.update d.stacks 263
      (SubexpQuarticFlatNeg.flat negative)⟩ : Data) := state_ext rfl hout
  have ht := hc.seq (he'.seq (hm.seq hz))
  rw [hfinal] at ht
  refine ⟨(28 * B + 5) + (n + ((24 * B + 6) + (8 * B + 3))),d₄.regs,?_,ht⟩
  change n ≤ 25000 * (B + 1)^2 at hn
  change _ ≤ 25000 * (B + 1)^2 + 60 * B + 14
  omega

theorem program_run (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (width : List Bool) (hw : width.length = baseWidth p μ) (d : Data)
    (hcurrent : d.stacks 259 = SubexpQuarticFlatNeg.flat a)
    (hservice : ∀ i, d.stacks (ports i) = blankStore minusOne.val M.bits width i)
    (h263 : d.stacks 263 = []) (h318 : d.stacks 318 = []) (h319 : d.stacks 319 = []) :
    ∃ rf : Fin 16 → Bool,
      RunsIn program (runtimeBound (baseWidth p μ) + 1)
        (d.withPC (some program.entry))
        ((⟨rf, Function.update d.stacks 263 (SubexpQuarticFlatNeg.flat
          (SubexpQuarticNegMachine.negateWords p μ M minusOne a))⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval p μ M a minusOne width hw d
    hcurrent hservice h263 h318 h319
  exact ⟨rf,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 259 263⟩

theorem negative_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (hminus : wordValue p μ minusOne = -1) (c : Fin 4 → ZMod (p^μ)) :
    quotientDenote c ((SubexpQuarticNegMachine.negateWords p μ M minusOne a).map
      (wordValue p μ)) = -quotientDenote c (a.map (wordValue p μ)) :=
  SubexpQuarticNegMachine.negateWords_quotient p μ M minusOne a hminus c

end SubexponentialSAT.SubexpCRTOuterNeg

end OAI.Algorithms
