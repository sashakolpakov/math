import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyPrefix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgramGateNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgramLift

namespace OAI.Algorithms

/-! The native head-stage gate and paid extraction of its prior-word prefix. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def gateRegisters (i : Fin 4) : Fin 16 := i.castAdd 12
def gatePorts : Fin 7 → Fin 48 := ![20,19,18,1,2,3,4]
def prefixRegisters (i : Fin 3) : Fin 16 := i.castAdd 13
def prefixPorts : Fin 11 → Fin 48 := ![8,18,10,1,2,3,4,5,6,7,13]

theorem gateRegisters_injective : Function.Injective gateRegisters := Fin.castAdd_injective _ _
theorem gatePorts_injective : Function.Injective gatePorts := by decide
theorem prefixRegisters_injective : Function.Injective prefixRegisters := Fin.castAdd_injective _ _
theorem prefixPorts_injective : Function.Injective prefixPorts := by decide

def prefixABI : PackingPrefixProgram.Ports 16 48 :=
  ⟨prefixRegisters,prefixPorts,prefixRegisters_injective,prefixPorts_injective⟩
abbrev gate : Cmd 16 48 :=
  liftCommand PackingWeightProgram.Gate.command 0 2 gateRegisters gatePorts
abbrev preparePrefix : Cmd 16 48 := PackingPrefixProgram.prepare prefixABI

abbrev headSetup : Cmd 16 48 := .seq gate preparePrefix

def SetupReady (d : Data) : Prop :=
  ∀ j : Fin 48,j ∈ ({1,2,3,4,5,6,7,13,18} : Finset (Fin 48)) → d.stacks j=[]

theorem gate_eval (d : Data) (h : SetupReady d) :
    ∃ t ≤ PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d)+1,
      ∃ e : Data, Eval gate t d e ∧
      e.stacks 18=(if (d.stacks 19).length < SubexponentialSAT.CounterPrograms.value (d.stacks 20)
        then d.stacks 19 else []) ∧
      (∀ j,j≠18→e.stacks j=d.stacks j) := by
  obtain ⟨t,ht,e,he,ho,hf,_⟩ := PackingWeightProgram.Gate.command_lifted
    gateRegisters gatePorts gateRegisters_injective gatePorts_injective d (by
      intro i hi
      fin_cases i <;> try (norm_num at hi)
      all_goals simpa [gatePorts] using h _ (by simp))
  exact ⟨t,ht,e,he,ho,hf⟩

theorem headSetup_eval {r Q : ℕ} (d : Data) (heads : ℕ) (fixed : List (Word r Q))
    (padding : List Bool) (hr : SetupReady d)
    (hhead : SubexponentialSAT.CounterPrograms.value (d.stacks 20)=heads)
    (hp : (d.stacks 19).length=fixed.length)
    (hw : (d.stacks 10).length=ReadPlan.wordWidth r Q)
    (ha : d.stacks 8=(fixed.reverse.map ReadPlan.encodeWord).flatten++padding) :
    ∃ t ≤ PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d)+1+
      PackingPrefixProgram.budget (headCount heads fixed) (ReadPlan.wordWidth r Q)+1,
      ∃ e : Data, Eval headSetup t d e ∧
      e.stacks 1=(headRows heads fixed).flatten ∧
      e.stacks 2=List.replicate (headCount heads fixed) true ∧
      (e.stacks 18).length=headCount heads fixed ∧
      (∀ j,j≠1→j≠2→j≠18→e.stacks j=d.stacks j) := by
  obtain ⟨tg,htg,b,hg,ho,hf⟩ := gate_eval d hr
  have hcount : (b.stacks 18).length=headCount heads fixed := by
    rw [ho,hhead,hp]
    simp only [headCount]
    split <;> simp [hp]
  have hb8 : b.stacks 8=d.stacks 8 := hf _ (by decide)
  have hb10 : (b.stacks 10).length=ReadPlan.wordWidth r Q := by rw [hf _ (by decide),hw]
  have hcapacity : (b.stacks 18).length*(b.stacks 10).length ≤ (b.stacks 8).length := by
    rw [hcount,hb10,hb8,ha,List.length_append,encodedWords_length,List.length_reverse]
    exact (Nat.mul_le_mul_right _ (headCount_le heads fixed)).trans (Nat.le_add_right _ _)
  obtain ⟨tp,htp,e,hep,he⟩ := PackingPrefixProgram.prepare_eval prefixABI b (by
    intro i hi
    fin_cases i <;> try (norm_num at hi)
    all_goals simpa [prefixABI,prefixPorts,hf] using hr _ (by simp)) hcapacity
  have ho1 : e.stacks 1=(headRows heads fixed).flatten := by
    have hh := hep.2.1
    change e.stacks 1=(b.stacks 8).take ((b.stacks 18).length*(b.stacks 10).length) at hh
    rw [hh,hcount,hb10,hb8,ha]
    exact take_headRows heads fixed padding
  have ho2 : e.stacks 2=List.replicate (headCount heads fixed) true := by
    have hh := hep.2.2.1
    simpa [prefixABI,prefixPorts,PackingPrefixProgram.unary,hcount] using hh
  have ho18 : (e.stacks 18).length=headCount heads fixed := by
    have hh := hep.1 1
    have hh' : e.stacks 18=b.stacks 18 := by simpa [prefixABI,prefixPorts] using hh
    exact (congrArg List.length hh').trans hcount
  refine ⟨tg+tp,?_,e,hg.seq he,ho1,ho2,ho18,?_⟩
  · change tp ≤ PackingPrefixProgram.budget (b.stacks 18).length (b.stacks 10).length+1 at htp
    rw [hcount,hb10] at htp
    omega
  · intro j hj1 hj2 hj18
    by_cases hm : ∃ i,prefixPorts i=j
    · obtain ⟨i,rfl⟩ := hm
      fin_cases i <;> first
        | exact False.elim (hj1 rfl)
        | exact False.elim (hj2 rfl)
        | exact False.elim (hj18 rfl)
        | exact (hep.1 0).trans (hf _ (by decide))
        | exact (hep.1 2).trans (hf _ (by decide))
        | exact (hep.2.2.2.1 (5 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (6 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (7 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (8 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (9 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
        | exact (hep.2.2.2.1 (10 : Fin 11) (by decide)).trans (hr _ (by simp [prefixPorts])).symm
    · exact (hep.2.2.2.2.1 j (by intro i hi; exact hm ⟨i,hi⟩)).trans (hf j hj18)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
