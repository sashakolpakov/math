import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramCache
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramCleanup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyScopeNative

namespace OAI.Algorithms

/-! Run the concrete weighted selector while retaining the literal width and
alphabet for the native packing-layout suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram

def selection : Code := .seq cacheInputs
  (.seq (.call (ProgramLinking.liftProgram
    (SequentialProgram.program PackingProgram.Assembly.command) id lowPorts))
    (.seq (saveHigh 8 62) clearLow))

def dataMass (d : Small) := ∑ i : Fin 48,(d.stacks i).length

theorem dataMass_bound (d : Small) (i : Fin 48) : (d.stacks i).length ≤ dataMass d := by
  unfold dataMass
  exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 48 => (d.stacks j).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)

def selectionSize (d : Small) (rows : List (List Bool)) :=
  dataMass d+rows.flatten.length+rows.length+1

def selectionBudget (d : Small) (rows : List (List Bool)) (controllerCost : ℕ) :=
  7*(d.stacks 10).length+5+(7*(d.stacks 39).length+5)+controllerCost+
    (7*rows.flatten.length+5)+48*(2*selectionSize d rows+3)

theorem selection_eval (outside : Store) (d : Small)
    (h52 : outside 52=[]) (h53 : outside 53=[]) (h54 : outside 54=[]) (h62 : outside 62=[])
    (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} [NeZero r] (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (s : ℕ) (hs : 0 < s)
    (hn : SubexponentialSAT.BinaryArithmetic.toNat (outside 56)=n)
    (hsb : SubexponentialSAT.BinaryArithmetic.toNat (outside 57)=s)
    (hmb : SubexponentialSAT.BinaryArithmetic.toNat (outside 58)=
      (PackingIncidenceInput.Semantics.nativeEntries scopes mask).length)
    (hrb : SubexponentialSAT.BinaryArithmetic.toNat (outside 59)=r)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail
      (n+PackingIncidenceInput.Semantics.factorCount scopes mask) [] d.stacks)
    (hc : (d.stacks 11).length=n+PackingIncidenceInput.Semantics.factorCount scopes mask)
    (he : SequentialProgram.HighState
      (PackingProgram.Assembly.Scope.env scopes n mask a tail
        (outside 56) (outside 57) (outside 58) (outside 59)) d.stacks) :
    let rows := PackingProgram.Assembly.Scope.rows scopes n mask hmask a tail s hs (NeZero.pos r)
    ∃ t rf, t ≤ selectionBudget d rows
      (PackingProgram.Assembly.Scope.cost scopes n mask a tail s
        (outside 56) (outside 57) (outside 58) (outside 59)) ∧
      Eval selection t (framed outside d)
        (framed (Function.update (cached outside (d.stacks 10) (d.stacks 39)) 62 rows.flatten)
          (⟨rf,fun _=>[]⟩ : Small)) := by
  dsimp only
  let rows := PackingProgram.Assembly.Scope.rows scopes n mask hmask a tail s hs (NeZero.pos r)
  let saved := cached outside (d.stacks 10) (d.stacks 39)
  obtain ⟨rc,hcache⟩ := cacheInputs_eval outside d h52 h53 h54
  obtain ⟨e,⟨nt,hnt,ht⟩,hfinished⟩ := PackingProgram.Assembly.Scope.run_output scopes n mask hmask
    a tail haN haC s hs (outside 56) (outside 57) (outside 58) (outside 59)
    hn hsb hmb hrb (setRegs d rc) hm hc he
  have hcall := framed_call (SequentialProgram.program PackingProgram.Assembly.command) saved ht
  obtain ⟨rs,hsave⟩ := saveHigh_eval saved e 8 62 (by decide) (by decide)
    (by simpa [saved] using h52) (by simpa [saved,cached] using h62)
  have hrows : e.stacks 8=rows.flatten := hfinished.1
  rw [hrows] at hsave
  obtain ⟨rf,hclear⟩ := clearLow_run (Function.update saved 62 rows.flatten) (setRegs e rs)
  have hinput : ∀ i,((setRegs d rc).stacks i).length ≤ selectionSize d rows := by
    intro i
    have h := dataMass_bound d i
    dsimp [setRegs,selectionSize]
    omega
  have hb := PackingProgram.Assembly.Scope.Finished.length_bound (rows := rows) (B := selectionSize d rows) hfinished
    hinput
    (by dsimp [selectionSize]; omega) (by dsimp [selectionSize]; omega)
  have hclean := clearLowBudget_le (setRegs e rs) (selectionSize d rows) hb
  refine ⟨(7*(d.stacks 10).length+5+(7*(d.stacks 39).length+5))+
      (nt+((7*rows.flatten.length+5)+clearLowBudget (setRegs e rs))),rf,?_,?_⟩
  · dsimp only [rows] at hclean ⊢
    dsimp only [selectionBudget]
    omega
  · exact hcache.seq (hcall.seq (hsave.seq hclear))

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
