import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramAdd
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramPorts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanServiceBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramLoops
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionPairSpec

namespace OAI.Algorithms

/-! Static native arithmetic readiness, independent of the final service
composition. The two polynomial caches do not participate in readiness. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod
variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

structure BaseReady (base : Store) (scalarWidth : List Bool)
    (frame : Fin 6 → List Bool) : Prop where
  high : ∀ j : Fin 32, j ≠ 8 → j ≠ 9 → base (RingCall.ports j) =
    (RingScan.serviceState (fun _ => false) M.bits [] [] [] [] scalarWidth
      cache.zero.val (RingTriple.tableEncoding table)).stacks j
  low : ∀ i : Fin 20,
    base (SubexponentialSAT.SubexpConvolutionPair.lowPort (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i)) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] scalarWidth [] frame).stacks i
  width : (base 104).length = degree * baseWidth p t
  scalarWidthLength : scalarWidth.length = baseWidth p t
  degreeLength : (base 204).length = degree
  scratch : base 120 = []
  work : ∀ j : Fin 256, 112 ≤ j.val → j.val ≤ 119 → base j = []


omit [Fact (Nat.Prime p)] in
/-- Readiness only inspects native arithmetic ports; the two protected
polynomial caches may vary while the native arithmetic frame is retained. -/
theorem BaseReady.frame_except_caches {base s : Store}
    {scalarWidth : List Bool} {frame : Fin 6 → List Bool}
    (H : BaseReady p t M cache table base scalarWidth frame)
    (hf : ∀ i : Fin 256, i.val < 205 → i ≠ 192 → i ≠ 193 → s i = base i) :
    BaseReady p t M cache table s scalarWidth frame := by
  constructor
  · intro i h8 h9
    have hp : (RingCall.ports i).val < 205 ∧ RingCall.ports i ≠ 192 ∧ RingCall.ports i ≠ 193 := by
      exact (by decide : ∀ j : Fin 32, (RingCall.ports j).val < 205 ∧
        RingCall.ports j ≠ 192 ∧ RingCall.ports j ≠ 193) i
    rw [hf _ hp.1 hp.2.1 hp.2.2]
    exact H.high i h8 h9
  · intro i
    have hp : (SubexponentialSAT.SubexpConvolutionPair.lowPort (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i)).val < 20 := i.isLt
    rw [hf _ (by omega) (by intro he; rw [he] at hp; norm_num at hp)
      (by intro he; rw [he] at hp; norm_num at hp)]
    exact H.low i
  · rw [hf 104 (by decide) (by decide) (by decide)]; exact H.width
  · exact H.scalarWidthLength
  · rw [hf 204 (by decide) (by decide) (by decide)]; exact H.degreeLength
  · rw [hf 120 (by decide) (by decide) (by decide)]; exact H.scratch
  · intro i hlo hhi
    rw [hf i (by omega) (by intro he; subst i; norm_num at hhi)
      (by intro he; subst i; norm_num at hhi)]
    exact H.work i hlo hhi

omit [Fact (Nat.Prime p)] in
theorem BaseReady.frame {base s : Store}
    {scalarWidth : List Bool} {frame : Fin 6 → List Bool}
    (H : BaseReady p t M cache table base scalarWidth frame)
    (hf : CRTLocalProgram.LowFrame base s) :
    BaseReady p t M cache table s scalarWidth frame :=
  BaseReady.frame_except_caches p t M cache table H (fun i hi _ _ => hf i hi)

omit [Fact (Nat.Prime p)] in
theorem BaseReady.update_cache {base : Store}
    {scalarWidth : List Bool} {frame : Fin 6 → List Bool}
    (H : BaseReady p t M cache table base scalarWidth frame)
    (i : Fin 256) (hi : i = 192 ∨ i = 193) (bits : List Bool) :
    BaseReady p t M cache table (Function.update base i bits) scalarWidth frame := by
  apply BaseReady.frame_except_caches p t M cache table H
  intro j _ h192 h193
  rcases hi with rfl | rfl
  · exact Function.update_of_ne h192 _ _
  · exact Function.update_of_ne h193 _ _


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec

end OAI.Algorithms
