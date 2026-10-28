import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramRun

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

variable {n h : ℕ}

def headIds (head : Fin h → Fin n) : List ℕ := List.ofFn (fun i => (head i).val)
def headBits (x : Fin h → Bool) : List Bool := List.ofFn x

theorem headIds_bound (head : Fin h → Fin n) : ∀ j ∈ headIds head,j < n := by
  intro j hj
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
  exact (head i).isLt

theorem headIds_nodup (head : Fin h → Fin n) (hinj : Function.Injective head) :
    (headIds head).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  exact hinj (Fin.ext hij)

theorem typed_mask_length (head : Fin h → Fin n) (x : Fin h → Bool) :
    (mask n (headIds head) (headBits x)).length=n :=
  mask_length n _ _ (headIds_bound head)

theorem typed_mask_head (head : Fin h → Fin n) (hinj : Function.Injective head)
    (x : Fin h → Bool) (i : Fin h) :
    (mask n (headIds head) (headBits x))[(head i).val]? = some (x i) := by
  apply mask_at n _ _ _ _ (headIds_bound head) (headIds_nodup head hinj)
  have hz : ((headIds head).zip (headBits x))[i.val]? = some ((head i).val,x i) := by
    apply List.getElem?_zip_eq_some.mpr
    constructor <;> simp [headIds,headBits,i.isLt]
  exact List.mem_of_getElem? hz

/-- Distinct head assignments have distinct full masks; no enumeration entry
is collapsed by the physical scatter. -/
theorem typed_mask_injective (head : Fin h → Fin n) (hinj : Function.Injective head) :
    Function.Injective (fun x : Fin h → Bool => mask n (headIds head) (headBits x)) := by
  intro x y hxy
  funext i
  have he := congrArg (fun bits : List Bool => bits[(head i).val]?) hxy
  dsimp only at he
  rw [typed_mask_head head hinj x i,typed_mask_head head hinj y i] at he
  exact Option.some.inj he

theorem typed_mask_off_head (head : Fin h → Fin n) (x : Fin h → Bool)
    (v : Fin n) (hv : v ∉ Set.range head) :
    (mask n (headIds head) (headBits x))[v.val]? = some false := by
  apply mask_outside n _ _ _ (headIds_bound head) v.isLt
  intro hm
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  exact hv ⟨i,Fin.ext hi⟩

/-- One fixed machine works for every ambient dimension and every ordered
injection supplied as framed unary identifiers. All three inputs survive. -/
theorem typed_program_runsIn (regs : Fin 8 → Bool) (head : Fin h → Fin n)
    (x : Fin h → Bool) :
    ∃ rf, RunsIn program (100*(n+1)*(h+1))
      ((input regs (headIds head) (headBits x) n).withPC (some program.entry))
      ((result rf (headIds head) (headBits x) n).withPC none) := by
  simpa [headIds,headBits] using program_runsIn regs n (headIds head) (headBits x)
    (by simp [headIds,headBits]) (headIds_bound head)

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
