import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticPowerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl
import OAI.Algorithms.SubexponentialSAT.SubexpActualRing
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! The fixed cache power call and selected-ring nilpotent-defect proof. -/

namespace SubexponentialSAT.SubexpLagrangeInverseCall

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 16 256
abbrev Code := Cmd 16 256
abbrev Store := Fin 256 → List Bool

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

def registers : Fin 8 ↪ Fin 16 := ⟨Fin.castAdd 8, Fin.castAdd_injective _ _⟩

def powerPorts (i : Fin 83) : Fin 256 :=
  if i = 78 then 225 else if i = 80 then 215 else if i = 81 then 216
  else if i = 82 then 219 else ⟨128 + i.val, by omega⟩

theorem powerPorts_injective : Function.Injective powerPorts := by decide

def inversePorts (i : Fin 96) : Fin 256 :=
  if i = 5 then 96 else if i = 10 then 97 else
  if i = 76 then 194 else if i = 82 then 205 else if i = 83 then 215 else
  if i = 84 then 201 else if i = 85 then 207 else if i = 86 then 211 else
  if i = 87 then 202 else if i = 88 then 224 else if i = 89 then 214 else
  i.castAdd 160

theorem inversePorts_injective : Function.Injective inversePorts := by decide

def inversePortEmbedding : Fin 96 ↪ Fin 256 := ⟨inversePorts, inversePorts_injective⟩

def seed : Code :=
  .call (ProgramLinking.liftProgram SubexpQuarticPowerProgram.program registers powerPorts)

/-- Native power workspace plus its six retained/control words. -/
structure PowerReady {B : ℕ} (modulus width exponent : List Bool)
    (t a one : Quad (Word B)) (s : Store) : Prop where
  native : ∀ i, s (powerPorts (SubexpQuarticPowerCore.native i)) =
    SubexpQuarticPowerProgram.cleanNative modulus (SubexpQuarticFlatMul.flat t) width i
  denominator : s 205 = SubexpQuarticFlatMul.flat a
  exponent : s 225 = exponent
  unit : s 207 = SubexpQuarticFlatMul.flat one
  seed : s 215 = []
  countdown : s 216 = []
  temporary : s 219 = []

theorem PowerReady.store {B : ℕ} {modulus width exponent : List Bool}
    {t a one : Quad (Word B)} {s : Store}
    (h : PowerReady modulus width exponent t a one s) (r : Fin 8 → Bool) :
    ∀ i, s (powerPorts i) =
      (SubexpQuarticPowerProgram.initial r modulus width exponent t a one).stacks i := by
  intro i
  refine Fin.addCases (m := 77) (n := 6) (fun j => ?_) (fun j => ?_) i
  · change s (powerPorts (SubexpQuarticPowerCore.native j)) =
      (SubexpQuarticPowerCore.initial r modulus width exponent t a one).stacks
        (SubexpQuarticPowerCore.native j)
    simpa only [SubexpQuarticPowerCore.initial, SubexpQuarticPowerCore.store_native]
      using h.native j
  · fin_cases j
    · change s 205 = SubexpQuarticFlatMul.flat a
      exact h.denominator
    · change s 225 = exponent
      exact h.exponent
    · change s 207 = SubexpQuarticFlatMul.flat one
      exact h.unit
    · change s 215 = []
      exact h.seed
    · change s 216 = []
      exact h.countdown
    · change s 219 = []
      exact h.temporary

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (v : α → γ)
    (s : β → γ) (h : ∀ i, s (f i) = v i) : Function.extend f v s = s := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

/-- A genuine power call, including preservation of every other native stack. -/
theorem seed_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p ^ μ)) (t a one : Quad (Word (baseWidth p μ)))
    (width exponent : List Bool) (hw : width.length = baseWidth p μ) (d : Data)
    (hready : PowerReady M.bits width exponent t a one d.stacks)
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (one.map (wordValue p μ)) = 1) :
    ∃ n rf b, n ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p μ) exponent ∧
      Eval seed n d ⟨Function.extend registers rf d.regs,
        Function.update d.stacks 215 (SubexpQuarticFlatMul.flat b)⟩ ∧
      quotientDenote c (b.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat exponent := by
  obtain ⟨rf, b, hv, _, n, hn, htrace⟩ := SubexpQuarticPowerProgram.run_value
    p μ M c t a one ht hu width exponent hw (d.regs ∘ registers)
  let start := SubexpQuarticPowerProgram.initial (d.regs ∘ registers) M.bits width exponent t a one
  have hsi : Function.extend powerPorts start.stacks d.stacks = d.stacks :=
    extend_agree ⟨powerPorts, powerPorts_injective⟩ _ _ (hready.store _)
  have hri : Function.extend registers (d.regs ∘ registers) d.regs = d.regs :=
    extend_agree registers _ _ (fun _ => rfl)
  have he := eval_call_lifted SubexpQuarticPowerProgram.program registers powerPorts d
    registers.injective powerPorts_injective htrace
  have hso : Function.extend powerPorts
      (Function.update start.stacks 80 (SubexpQuarticFlatMul.flat b)) d.stacks =
      Function.update d.stacks 215 (SubexpQuarticFlatMul.flat b) := by
    rw [ProgramLinking.extend_update powerPorts_injective, hsi]
    rfl
  refine ⟨n, rf, b, hn, ?_, hv⟩
  change Eval seed n
    ⟨Function.extend registers (d.regs ∘ registers) d.regs,
      Function.extend powerPorts start.stacks d.stacks⟩
    ⟨Function.extend registers rf d.regs,
      Function.extend powerPorts (Function.update start.stacks 80 (SubexpQuarticFlatMul.flat b))
        d.stacks⟩ at he
  rw [hri, hsi, hso] at he
  exact he

noncomputable def denote (p μ : ℕ) [Fact p.Prime] (a : Quad (Word (baseWidth p μ))) :
    SubexpActualRing.Ring p μ :=
  quotientDenote (QuarticSearch.liftedCoefficients p μ) (a.map (wordValue p μ))

theorem defect_nilpotent (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (a : Quad (Word (baseWidth p μ)))
    (ha : SubexpActualRing.rho p μ hμ (denote p μ a) ≠ 0) :
    (1 - denote p μ a * denote p μ a ^ (p ^ 4 - 2)) ^ μ = 0 :=
  SubexpResidueInverse.fermat_defect_nilpotent (SubexpActualRing.rho p μ hμ) (p ^ 4)
    (SubexpActualRing.extension_card p) (p : SubexpActualRing.Ring p μ) μ
    (SubexpActualRing.prime_power_zero p μ)
    (fun x hx => (SubexpActualRing.rho_eq_zero_iff p μ hμ x).mp hx) (denote p μ a) ha


end SubexponentialSAT.SubexpLagrangeInverseCall

end OAI.Algorithms
