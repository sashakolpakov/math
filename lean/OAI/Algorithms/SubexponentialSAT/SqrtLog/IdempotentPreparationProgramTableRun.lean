import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramTable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramEntryRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramSerialization

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open IdempotentTableEntryProgram (entryCode)

def cachedEntry (base : Fin 41 → List Bool) (i j k : ℕ) : List Bool :=
  base (entrySource (entryCode i j k))

abbrev nativeTable : Cmd 8 41 := Scan.tableCommand entryCommand

theorem nativeTable_eval (d : Data) (n B : ℕ)
    (h37 : d.stacks 37 = List.replicate n true)
    (h24 : d.stacks 24 = []) (h25 : d.stacks 25 = [])
    (h26 : d.stacks 26 = []) (h38 : d.stacks 38 = [])
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = [])
    (hw : ∀ c, (d.stacks (entrySource c)).length ≤ B) :
    ∃ cost rf, cost ≤ Scan.tableBudget n (200*(n+B+1)) ∧
      Eval nativeTable cost d ⟨rf,Function.update d.stacks 22
        (Scan.tableCells (cachedEntry d.stacks) n ++ d.stacks 22)⟩ := by
  suffices step : ∀ i, i < n → ∀ j, j < n → ∀ k, k < n → ∀ regs tail,
      ∃ cost rf, cost ≤ 200*(n+B+1) ∧
        Eval entryCommand cost (Scan.tripleState d.stacks regs i j k tail)
          (Scan.tripleState d.stacks rf i j k (cachedEntry d.stacks i j k ++ tail)) by
    obtain ⟨cost,rf,hcost,he⟩ := Scan.tableCommand_eval d.stacks entryCommand
      (cachedEntry d.stacks) n (200*(n+B+1)) h37 h24 h25 h26 h38 step d.regs (d.stacks 22)
    refine ⟨cost,rf,hcost,?_⟩
    simpa [nativeTable] using he
  intro i hi j hj k hk regs tail
  let a := Scan.tripleState d.stacks regs i j k tail
  obtain ⟨cost,rf,hcost,he⟩ := entryCommand_eval a i j k
    (by simp [a,Scan.tripleState]) (by simp [a,Scan.tripleState])
    (by simp [a,Scan.tripleState]) (by simp [a,Scan.tripleState,h0])
    (by simp [a,Scan.tripleState,h1]) (by simp [a,Scan.tripleState,h2])
    (by simp [a,Scan.tripleState,h3]) (by simp [a,Scan.tripleState,h4])
  have hsource : a.stacks (entrySource (entryCode i j k)) =
      cachedEntry d.stacks i j k := by
    change a.stacks (entrySource (entryCode i j k)) = d.stacks (entrySource (entryCode i j k))
    generalize entryCode i j k = code
    fin_cases code <;> simp [a,Scan.tripleState,entrySource]
  refine ⟨cost,rf,?_,?_⟩
  · rw [hsource] at hcost
    have hw' := hw (entryCode i j k)
    dsimp [cachedEntry] at hcost
    omega
  · have ha22 : a.stacks 22=tail := by simp [a,Scan.tripleState]
    rw [hsource,ha22] at he
    simpa [a,Scan.tripleState,Function.update_idem] using he

namespace Scan

theorem cells_eq_ofFn (f : ℕ → List Bool) (n : ℕ) :
    cells f n = (List.ofFn (fun i : Fin n => f i.val)).flatten := by
  induction n with
  | zero => simp [cells]
  | succ n ih =>
      rw [cells,List.ofFn_succ']
      simp only [List.concat_eq_append,List.flatten_append,List.flatten_cons,
        List.flatten_nil,List.append_nil,Fin.val_castSucc,Fin.val_last]
      rw [ih]

theorem tableCells_eq_tableTape {n B : ℕ} (f : ℕ → ℕ → ℕ → List Bool)
    (table : Fin n → Fin n → Fin n → SubexpQuarticRing.Word B)
    (h : ∀ i j k : Fin n, f i.val j.val k.val = (table i j k).val) :
    tableCells f n = IdempotentProgram.tableTape table := by
  simp only [tableCells,cells_eq_ofFn]
  simp only [h]
  simp [IdempotentProgram.tableTape,IdempotentProgram.tableWords,List.map_flatten,
    List.flatten_flatten,List.map_ofFn,Function.comp_def]

end Scan

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
