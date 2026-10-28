import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeIndexEncoding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSparse
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramScan

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

@[simp] theorem encodeMask_empty (n : ℕ) :
    encodeMask (∅ : Finset (Fin n)) = List.replicate n false := by
  apply List.ext_getElem <;> simp [encodeMask]

def ofIndex {n : ℕ} (a : Index (Fin n) × List Bool) : Entry :=
  ⟨a.1.u,a.1.z,encodeMask a.1.vars,a.2⟩

theorem raw_ofIndex {n : ℕ} (l : List (Index (Fin n) × List Bool)) :
    raw (l.map ofIndex) = Squarefree.Program.rawEntries
      (l.map fun a => (encodeIndex a.1,a.2)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [raw,Squarefree.Program.rawEntries,ofIndex,Entry.bits,
      recordBits,keyBits,encodeIndex,ih,List.append_assoc]

theorem selected_ofIndex {n : ℕ} (s : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) :
    selected (encodeMask s) (l.map ofIndex) = (Moments.rawProject s l).map ofIndex := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have he : encodeMask a.1.vars = encodeMask s ↔ a.1.vars=s :=
        encodeMask_injective.eq_iff
      by_cases h : a.1.vars=s
      · simp [selected,ofIndex,h,Moments.rawProject,ih,Entry.erased,encodeMask_empty]
      · simp [selected,ofIndex,he,h,Moments.rawProject,ih]

/-- Actual machine output, expressed in the raw dictionary ABI used by moments. -/
theorem raw_dictionary_runsIn {n : ℕ} (s : Finset (Fin n))
    (l : List (Index (Fin n) × List Bool)) (regs : Fin 5 → Bool) :
    ∃ rf, RunsIn program
      (200*((Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))).length+1)*(n+2)+1)
      ((machine regs {input:=Encoding.frame (encodeMask s)++
        Squarefree.Program.rawEntries (l.map fun a => (encodeIndex a.1,a.2))}).withPC (some program.entry))
      ((machine rf {target:=(encodeMask s).reverse,framed:=
        Squarefree.Program.rawEntries ((Moments.rawProject s l).map fun a => (encodeIndex a.1,a.2))}).withPC none) := by
  simpa [input,raw_ofIndex,selected_ofIndex] using serializedEval regs (encodeMask s) (l.map ofIndex)

/-- Erasing the common support is injective on retained keys. -/
theorem erased_key_injective {V : Type*} {s : Finset V} {a b : Index V}
    (ha : a.vars=s) (hb : b.vars=s)
    (he : (⟨a.u,a.z,∅⟩ : Index V) = ⟨b.u,b.z,∅⟩) : a=b := by
  have hu := congrArg Index.u he
  have hz := congrArg Index.z he
  cases a; cases b
  simp_all

theorem mem_rawProject {V R : Type*} [DecidableEq V] (s : Finset V)
    (l : List (Index V × R)) (b : Index V × R) :
    b ∈ Moments.rawProject s l →
      ∃ a ∈ l, a.1.vars=s ∧ b=(⟨a.1.u,a.1.z,∅⟩,a.2) := by
  induction l with
  | nil => simp [Moments.rawProject]
  | cons a l ih =>
      by_cases h : a.1.vars=s
      · simp only [Moments.rawProject,h,ite_true,List.mem_cons]
        intro hb
        rcases hb with rfl | hb
        · exact ⟨a,by simp,h,rfl⟩
        · obtain ⟨c,hc,hcs,hbc⟩ := ih hb
          exact ⟨c,by simp [hc],hcs,hbc⟩
      · simp only [Moments.rawProject,h,ite_false]
        intro hb
        obtain ⟨c,hc,hcs,hbc⟩ := ih hb
        exact ⟨c,by simp [hc],hcs,hbc⟩

/-- A unique-key dictionary remains unique-key after exact-support projection;
no normalization call or coefficient additions are required. -/
theorem rawProject_keys_nodup {V R : Type*} [DecidableEq V]
    (s : Finset V) (l : List (Index V × R))
    (h : (l.map Prod.fst).Nodup) :
    ((Moments.rawProject s l).map Prod.fst).Nodup := by
  induction l with
  | nil => simp [Moments.rawProject]
  | cons a l ih =>
      simp only [List.map_cons,List.nodup_cons] at h
      by_cases hs : a.1.vars=s
      · simp only [Moments.rawProject,hs,ite_true,List.map_cons,List.nodup_cons]
        refine ⟨?_,ih h.2⟩
        intro hm
        obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
        obtain ⟨c,hc,hcs,hbc⟩ := mem_rawProject s l b hb
        subst b
        have hac : a.1=c.1 := erased_key_injective hs hcs he.symm
        exact h.1 (List.mem_map.mpr ⟨c,hc,hac.symm⟩)
      · simpa [Moments.rawProject,hs] using ih h.2

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
