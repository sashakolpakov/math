import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReadyCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyInputReady
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness

namespace OAI.Algorithms

/-! The arithmetic half of physical source readiness is preserved by source
control copies. The source-count initializer uses R+1, independently of J. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def rawLow (a : Data) : Fin 256 → List Bool := a.stacks ∘ localPort ∘ executorPorts

/-- Native arithmetic inspects only these unchanged local stacks. -/
def arithmeticPort (i : Fin 256) : Prop :=
  (i.val < 21 ∨ i=104 ∨ (112 ≤ i.val ∧ i.val ≤ 204)) ∧ i≠192 ∧ i≠193
instance (i : Fin 256) : Decidable (arithmeticPort i) := inferInstanceAs
  (Decidable ((i.val < 21 ∨ i=104 ∨ (112 ≤ i.val ∧ i.val ≤ 204)) ∧ i≠192 ∧ i≠193))

theorem arithmetic_frame (a : Data) (i : Fin 256) (hi : arithmeticPort i) :
    localStore a (executorPorts i)=rawLow a i := by
  apply local_frame
  intro hm
  simp only [changedLocal, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hi with ⟨hi, h192, h193⟩
  rcases hm with hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|
    hm|hm|hm|hm|hm|hm|hm|hm|hm
  all_goals
    have hv := congrArg Fin.val hm
    simp [executorPorts] at hv
    rcases hi with hi | hi | hi
    · omega
    · subst i
      norm_num at hv
    · omega

theorem arithmetic_ready {t d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : Data) (h : PerturbationAssembly.ArithmeticInput t model M cache (rawLow a)) :
    PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t model M cache)
      (localStore a ∘ executorPorts) (rawLow a 10) (fun _ => []) := by
  have H := h.pairReady
  constructor
  · intro i hi hj
    rw [Function.comp_apply,arithmetic_frame a _
      ((by decide : ∀ j : Fin 32,arithmeticPort (RingCall.ports j)) i)]
    exact H.high i hi hj
  · intro i
    rw [Function.comp_apply,arithmetic_frame a _
      ((by decide : ∀ j : Fin 20,arithmeticPort
        (SubexpConvolutionPair.lowPort (SubexpJetCellProgram.scalarPorts j))) i)]
    exact H.low i
  · rw [Function.comp_apply,arithmetic_frame a 104 (by decide)]; exact H.width
  · exact H.scalarWidthLength
  · rw [Function.comp_apply,arithmetic_frame a 204 (by decide)]; exact H.degreeLength
  · rw [Function.comp_apply,arithmetic_frame a 120 (by decide)]; exact H.scratch
  · intro i hlo hhi
    rw [Function.comp_apply,arithmetic_frame a i (by
      unfold arithmeticPort; constructor
      · exact Or.inr (Or.inr ⟨hlo,by omega⟩)
      · constructor <;> intro he <;> subst i <;> norm_num at hhi)]
    exact H.work i hlo hhi

theorem initialized_ready {t d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : Data) (D : ℕ)
    (h : PerturbationAssembly.ArithmeticInput t model M cache (rawLow a))
    (hD : a.stacks (localPort 210)=List.replicate D true)
    (h245 : a.stacks (localPort 245)=[]) :
    LayoutSourceRowsProgramInitialize.Ready (localStore a ∘ initializationPorts)
      D (d*baseWidth 3 t) := by
  have hc (i : Fin 256) (hi : i ∈ ([100,101,102,107,108,120] : List (Fin 256))) :
      localStore a (initializationPorts i)=[] := by
    rw [local_frame a _ (by
      intro hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
        norm_num [initializationPorts, changedLocal] at hm)]
    apply h.clean
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
    · intro hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
        norm_num [PerturbationAssembly.arithmeticCachePorts] at hm
  refine ⟨?_,?_,hc 100 (by decide),hc 101 (by decide),hc 102 (by decide),
    hc 107 (by decide),hc 108 (by decide),hc 120 (by decide),?_,?_,?_,?_,?_⟩
  · exact (local_frame a 210 (by decide)).trans hD
  · exact (local_frame a 104 (by decide)).trans h.fullZero
  · exact local_cache a 192 (by decide)
  · exact local_cache a 193 (by decide)
  · exact local_cache a 242 (by decide)
  · exact local_cache a 243 (by decide)
  · exact (local_frame a 245 (by decide)).trans h245

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
