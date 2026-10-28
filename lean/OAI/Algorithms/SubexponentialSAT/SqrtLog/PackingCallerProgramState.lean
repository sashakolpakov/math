import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramStage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramExportFacts

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Sources (a : Wide.Data) (p : Problem) : Prop where
  scopes : a.stacks 718=Scan.scopeBits p.scopes
  ambientUnary : a.stacks 128=Scan.unary p.n
  mask : a.stacks 719=p.mask
  ambient : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 709)=p.n
  coordinate : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 720)=p.Q
  radius : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 721)=p.r
  epsilon : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 722)=p.s
  incidence : SubexponentialSAT.BinaryArithmetic.toNat (a.stacks 723)=p.incidences

structure Empty (a : Wide.Data) : Prop where
  bank : Wide.BankEmpty (Wide.project a)
  temporary : a.stacks 684=[]
  words : a.stacks 133=[]
  metadata : a.stacks 135=[]
  plans : a.stacks 136=[]
  parked : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[]

theorem Sources.parameters {a : Wide.Data} {p : Problem} (h : Sources a p) :
    Parameters (Wide.parameterStore (Wide.project a)) p := by
  exact ⟨by simpa [Wide.parameterStore,Wide.project] using h.ambient,
    by simpa [Wide.parameterStore,Wide.project] using h.radius,
    by simpa [Wide.parameterStore,Wide.project] using h.coordinate,
    by simpa [Wide.parameterStore,Wide.project] using h.epsilon,
    by simpa [Wide.parameterStore,Wide.project] using h.incidence⟩

theorem parameters_workspace (a : Wide.Data) : Workspace (Wide.parameterStore (Wide.project a)) := by
  constructor <;> simp [Wide.parameterStore]

noncomputable def bankOutput (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) : Local :=
  framed (outputStore (Wide.parameterStore (Wide.project a)) p w tail)
    (⟨fun _=>false,fun _=>[]⟩ : Small)

noncomputable def middle (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) : Wide.Local :=
  ⟨fun _=>false,fun i=>if hi : 417 ≤ i.val ∧ i.val < 481
    then (bankOutput a p w tail).stacks ⟨i.val-417,by omega⟩ else a.stacks i⟩

theorem middle_bank (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 64) :
    (middle a p w tail).stacks (Wide.ports i)=(bankOutput a p w tail).stacks i := by
  have hi := i.isLt
  have hport : 417 ≤ (Wide.ports i).val ∧ (Wide.ports i).val < 481 := by
    simp only [Wide.ports_val]
    omega
  simp only [middle]
  rw [dite_eq_left hport]
  apply congrArg (bankOutput a p w tail).stacks
  apply Fin.ext
  simp only [Wide.ports_val]
  omega

theorem middle_frame (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) (i : Fin 768)
    (hi : i.val < 417 ∨ 481 ≤ i.val) : (middle a p w tail).stacks i=a.stacks i := by
  simp [middle,show ¬(417 ≤ i.val ∧ i.val < 481) by omega]

theorem middle_words (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (middle a p w tail).stacks (Wide.ports 62)=((p.words w tail).map ReadPlan.encodeWord).flatten := by
  rw [middle_bank]
  simp [bankOutput,framed_stack,outputStore,selectedStore]

theorem middle_metadata (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (middle a p w tail).stacks (Wide.ports 63)=(p.spec w tail).suffix.metadata := by
  rw [middle_bank]
  simp [bankOutput,framed_stack,outputStore]

theorem middle_plans (a : Wide.Data) (p : Problem)
    (w : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (middle a p w tail).stacks (Wide.ports 61)=planBits p.scopes p.n p.mask := by
  rw [middle_bank]
  simp [bankOutput,framed_stack,outputStore,selectedStore,cached,loadedStore,planStore]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
