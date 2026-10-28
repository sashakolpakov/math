import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheProgram

namespace OAI.Algorithms

/-! An injective caller interface for the complete physical cache kernel. -/

namespace SubexponentialSAT.SubexpFieldCacheCall

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpCRTCofactorControl SubexpFieldCacheControl
open SubexpQuarticFlatMul (flat)
open SubexpFieldCacheNodeLoop (PowerValue negativeBytes)
open SubexpFieldCachePairLoop (PairValue)
open SubexpFieldCacheProgram (negativeWords resultFrame budget)

def programAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s) :=
  ProgramLinking.liftProgram SubexpFieldCacheMachine.program registers ports

abbrev callAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s) : Cmd r s :=
  .call (programAt registers ports)

def resultStacks {s : ℕ} (ports : Fin 110 ↪ Fin s)
    (nodes inverses negatives differences : List Bool) (stk : Fin s → List Bool) :=
  Function.update (Function.update (Function.update (Function.update stk
    (ports 97) nodes) (ports 98) inverses) (ports 100) negatives) (ports 103) differences

theorem resultStacks_frame {s : ℕ} (ports : Fin 110 ↪ Fin s)
    (nodes inverses negatives differences : List Bool) (stk : Fin s → List Bool) (j : Fin s)
    (h97 : j ≠ ports 97) (h98 : j ≠ ports 98)
    (h100 : j ≠ ports 100) (h103 : j ≠ ports 103) :
    resultStacks ports nodes inverses negatives differences stk j = stk j := by
  simp only [resultStacks, Function.update_of_ne h103, Function.update_of_ne h100,
    Function.update_of_ne h98, Function.update_of_ne h97]

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

theorem local_stacks_update (frame : Fin 110 → List Bool) (base : Words)
    (nodes inverses negatives differences : List Bool) :
    store (resultFrame frame nodes negatives differences)
      (SubexpFieldCacheNodeLoop.ready base [] inverses) =
    Function.update (Function.update (Function.update (Function.update
      (store frame (SubexpFieldCacheNodeLoop.ready base [] [])) 97 nodes)
        98 inverses) 100 negatives) 103 differences := by
  symm
  rw [update_store_extra _ _ 97 _ (by left; rfl), update_store_accumulator,
    update_store_extra _ _ 100 _ (by right; left; rfl),
    update_store_extra _ _ 103 _ (by right; right; left; rfl)]
  rfl

/-- All assignments are static injective wiring. The caller supplies actual
framed node records; only its four mapped result ports change on return. -/
theorem callAt_value {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hmone : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ) (hblock : base.blockWidth = [])
    (hB : 0 < baseWidth p μ) (xs : List (Quad (Word (baseWidth p μ))))
    (d : State r s) (frame : Fin 110 → List Bool)
    (hsource : frame 97 = ProgramEncoding.encodeRecords (xs.map flat))
    (hnegative : frame 100 = []) (hdifference : frame 103 = []) (houter : frame 106 = [])
    (hstore : ∀ i, d.stacks (ports i) =
      store frame (SubexpFieldCacheNodeLoop.ready base [] []) i) :
    ∃ n rf ys rows, n ≤ budget (baseWidth p μ) base.exponent xs.length + 1 ∧
      List.Forall₂ (PowerValue p μ c base.exponent) xs ys ∧
      List.Forall₂ (fun node row => List.Forall₂ (PairValue p μ c base.exponent node)
        (negativeWords p μ M minusOne xs) row) xs rows ∧
      Eval (callAt registers ports) n d
        ⟨Function.extend registers rf d.regs,
          resultStacks ports (xs.flatMap flat) (ys.flatMap flat)
            (negativeBytes p μ M minusOne xs) (rows.flatten.flatMap flat) d.stacks⟩ := by
  obtain ⟨rf, ys, rows, hys, hrows, n, hn, ht⟩ := SubexpFieldCacheProgram.program_value
    p μ M c t unit minusOne ht hu base hm hr hone hmone hw hblock hB xs
    (fun i => d.regs (registers i)) frame hsource hnegative hdifference houter
  have he := eval_call_lifted SubexpFieldCacheMachine.program registers ports d
    registers.injective ports.injective ht
  have hi := extend_agree ports (store frame (SubexpFieldCacheNodeLoop.ready base [] []))
    d.stacks hstore
  have hir := extend_agree registers (fun i => d.regs (registers i)) d.regs (fun _ => rfl)
  have ho : Function.extend ports
      (store (resultFrame frame (xs.flatMap flat) (negativeBytes p μ M minusOne xs)
        (rows.flatten.flatMap flat)) (SubexpFieldCacheNodeLoop.ready base [] (ys.flatMap flat)))
      d.stacks = resultStacks ports (xs.flatMap flat) (ys.flatMap flat)
        (negativeBytes p μ M minusOne xs) (rows.flatten.flatMap flat) d.stacks := by
    rw [local_stacks_update, ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, hi]
    rfl
  refine ⟨n, rf, ys, rows, hn, hys, hrows, ?_⟩
  simpa only [callAt, programAt, embedState, state, hi, hir, ho] using he

end SubexponentialSAT.SubexpFieldCacheCall

end OAI.Algorithms
