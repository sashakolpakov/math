import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScanPreserve

namespace OAI.Algorithms

/-! Exact natural-code interfaces for the fixed encoded relation scanner. -/
namespace SubexponentialSAT.ExecClauseRelationScan
open BitProgram StructuredCalls

def codeClause (C : List ℕ) : Clause := C.map Encoding.encodeNat
def codeFormula (F : List (List ℕ)) : Formula := F.map codeClause

def codeTest (mode : Mode) (C Q : List ℕ) : Bool :=
  match mode with
  | .equivalent => ExecCNF.equivalent C Q
  | .strictSubset => ExecCNF.strictSubset C Q
  | .missingCore => !(ExecCNF.subset Q C)

theorem test_codes (mode : Mode) (C Q : List ℕ) :
    test mode (codeClause C) (codeClause Q) = codeTest mode C Q := by
  cases mode <;>
    simp only [test, codeTest, codeClause,
      ExecClauseRelationsProgram.equivalent_map_injective Encoding.encodeNat
        Encoding.encodeNat_injective,
      ExecClauseRelationsProgram.strictSubset_map_injective Encoding.encodeNat
        Encoding.encodeNat_injective,
      ExecClauseRelationsProgram.subset_map_injective Encoding.encodeNat
        Encoding.encodeNat_injective]

theorem encodeClause_codes (C : List ℕ) :
    encodeClause (codeClause C) = Encoding.encodeList Encoding.encodeNat C :=
  ExecClauseRelationsProgram.encodeList_id_map _ _

theorem encodeFormula_codes (F : List (List ℕ)) :
    encodeFormula (codeFormula F) =
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp only [encodeFormula, codeFormula, List.map_cons, Encoding.encodeList,
      encodeClause_codes]
    exact congrArg (fun tail => true :: Encoding.frame
      (Encoding.encodeList Encoding.encodeNat C) ++ tail) ih

theorem any_codes (mode : Mode) (F : List (List ℕ)) (Q : List ℕ) :
    (codeFormula F).any (fun C => test mode C (codeClause Q)) =
      F.any (fun C => codeTest mode C Q) := by
  simp [codeFormula, List.any_map, Function.comp_def, test_codes]

namespace Preserving

def codeInvariant (F : List (List ℕ)) (Q : List ℕ) (d : Data) : Prop :=
  d.stacks 12 = Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F ∧
    d.stacks 9 = Encoding.encodeList Encoding.encodeNat Q ∧
    (∀ i : Fin 9, d.stacks (Fin.castAdd 4 i) = []) ∧ d.stacks 10 = []

theorem codeInvariant_iff (F : List (List ℕ)) (Q : List ℕ) (d : Data) :
    codeInvariant F Q d ↔ invariant (codeFormula F) (codeClause Q) d := by
  simp only [codeInvariant, invariant, ExecClauseRelationScan.invariant,
    encodeFormula_codes, encodeClause_codes, restrict, stackPort,
    Function.comp_apply, and_assoc]
  rfl

def codeBound (F : List (List ℕ)) (Q : List ℕ) : ℕ :=
  512 * ((Encoding.encodeList Encoding.encodeNat Q).length + 1) *
    ((Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F).length + 1)

theorem nat_program_runsIn (mode : Mode) (F : List (List ℕ)) (Q : List ℕ) (d : Data)
    (valid : codeInvariant F Q d) (hout : d.stacks 11 = []) :
    ∃ e : Data, RunsIn (program mode) (codeBound F Q)
      (d.withPC (some (program mode).entry)) (e.withPC none) ∧ codeInvariant F Q e ∧
      e.regs 14 = F.any (fun C => codeTest mode C Q) ∧
      e.stacks 11 = [F.any (fun C => codeTest mode C Q)] := by
  have hv := (codeInvariant_iff F Q d).mp valid
  obtain ⟨e, he, hv, hr, hp⟩ := program_runsIn mode (codeFormula F) (codeClause Q) d hv hout
  refine ⟨e, ?_, (codeInvariant_iff F Q e).mpr hv, ?_, ?_⟩
  · simpa only [bound, codeBound, encodeFormula_codes, encodeClause_codes] using he
  · simpa only [any_codes] using hr
  · simpa only [any_codes] using hp

end Preserving
end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
