import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgramVisit

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def chosenIds (p : ℕ → Bool) (n : ℕ) : List ℕ := (List.range n).filter p
def count (p : ℕ → Bool) (n : ℕ) : ℕ := (chosenIds p n).length

def recordPrefix (p : ℕ → Bool) (n : ℕ) : List Bool := (chosenIds p n).flatMap natRecord

theorem prefix_succ (p : ℕ → Bool) (n : ℕ) :
    recordPrefix p (n+1) = recordPrefix p n ++ (if p n then natRecord n else []) := by
  simp only [recordPrefix, chosenIds, List.range_succ, List.filter_append, List.flatMap_append]
  cases hp : p n <;> simp [hp]

theorem records_prefix (xs : List ℕ) :
    xs.flatMap natRecord ++ [false] = ProgramEncoding.encodeRecords (xs.map Encoding.encodeNat) := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    change (natRecord j ++ xs.flatMap natRecord) ++ [false] =
      natRecord j ++ ProgramEncoding.encodeRecords (xs.map Encoding.encodeNat)
    rw [List.append_assoc, ih]

theorem prefix_encode (p : ℕ → Bool) (n : ℕ) :
    recordPrefix p n ++ [false] = ProgramEncoding.encodeRecords ((chosenIds p n).map Encoding.encodeNat) :=
  records_prefix _

theorem count_succ (p : ℕ → Bool) (n : ℕ) :
    count p (n+1)=count p n+(if p n then 1 else 0) := by
  simp only [count,chosenIds,List.range_succ,List.filter_append,List.length_append]
  cases hp : p n <;> simp [hp]

def loopPorts : UnaryForPrograms.Ports 16 64 := ⟨39,14,15⟩
def loop : Code := UnaryForPrograms.forCmd loopPorts visit

theorem visitBound_mono {a b : ℕ} (hab : a ≤ b) (A W z : ℕ) :
    visitBound A a W z ≤ visitBound A b W z := by
  unfold visitBound lookupCost
  gcongr

/-- Descending physical visits prepend records, so the resulting list is in
ascending original-factor order. Every visit is discharged by visit_row. -/
theorem loop_visits (rows : List (List Bool)) (A W z : ℕ)
    (hrows : ∀ row ∈ rows,row.length=W) (n : ℕ) :
    ∀ d : Data, A + n ≤ rows.length → d.stacks 33=rows.flatten → d.stacks 31=unary A →
      d.stacks 32=unary z → d.stacks 38=unary W → d.stacks 39=unary n → Clean d →
    ∃ costs ticks e, UnaryForPrograms.Visits loopPorts visit costs ticks d e ∧
      ticks ≤ n*(visitBound A rows.length W z+2)+2 ∧
      e.stacks=Function.update (Function.update (Function.update d.stacks 39 [])
        0 (recordPrefix (predicate rows A z) n++d.stacks 0))
        1 (zeros (count (predicate rows A z) n)++d.stacks 1) := by
  induction n with
  | zero =>
      intro d _ hs hA hz hw hn hc
      refine ⟨[],2,UnaryForPrograms.popped loopPorts d,.done d hn,by simp,?_⟩
      funext i
      by_cases h0 : i=0
      · subst i; simp [UnaryForPrograms.popped,loopPorts,recordPrefix,count,chosenIds]
      by_cases h1 : i=1
      · subst i; simp [UnaryForPrograms.popped,loopPorts,recordPrefix,count,chosenIds]
      by_cases h39 : i=39
      · subst i; simp [UnaryForPrograms.popped,loopPorts,hn]
      · simp [UnaryForPrograms.popped,loopPorts,h0,h1,h39]
  | succ n ih =>
      intro d hnd hs hA hz hw hn hc
      have hlt : A+n < rows.length := by omega
      let p := UnaryForPrograms.popped loopPorts d
      have hp39 : p.stacks 39=unary n := by
        simp [p,UnaryForPrograms.popped,loopPorts,hn,List.replicate_succ]
      have hp33 : p.stacks 33=rows.flatten := by simp [p,UnaryForPrograms.popped,loopPorts,hs]
      have hp31 : p.stacks 31=unary A := by simp [p,UnaryForPrograms.popped,loopPorts,hA]
      have hp32 : p.stacks 32=unary z := by simp [p,UnaryForPrograms.popped,loopPorts,hz]
      have hp38 : p.stacks 38=unary W := by simp [p,UnaryForPrograms.popped,loopPorts,hw]
      have hpc : Clean p := by
        intro i hi
        have hne : i ≠ 39 := by intro he; subst i; simp at hi
        simpa [p,UnaryForPrograms.popped,loopPorts,hne] using hc i hi
      obtain ⟨nv,e,hnv,hev,hes⟩ := visit_row rows A W z n p hrows hlt hp33 hp31 hp32 hp38 hp39 hpc
      have hnv' : nv ≤ visitBound A rows.length W z :=
        hnv.trans (visitBound_mono (by omega) A W z)
      have he39 : e.stacks 39=unary n := by simp [hes,hp39]
      obtain ⟨costs,nt,f,hv,hnt,hfs⟩ := ih e (by omega)
        (by simp [hes,hp33]) (by simp [hes,hp31]) (by simp [hes,hp32])
        (by simp [hes,hp38]) he39 (clean_outputs p e hpc _ _ hes)
      refine ⟨nv::costs,nv+nt+2,f,
        .step (by simp [loopPorts,hn]) hev (by simp [hes,loopPorts,p]) hv,?_,?_⟩
      · rw [Nat.succ_mul]
        omega
      · funext i
        by_cases h0 : i=0
        · subst i
          cases hp : predicate rows A z n <;>
            simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,
              prefix_succ,hp,List.append_assoc]
        by_cases h1 : i=1
        · subst i
          cases hp : predicate rows A z n <;>
            simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,count_succ,hp,
              zeros,List.replicate_succ',List.append_assoc]
        by_cases h39 : i=39
        · subst i; simp [hfs]
        · simp [hfs,hes,p,UnaryForPrograms.popped,loopPorts,h0,h1,h39]

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
