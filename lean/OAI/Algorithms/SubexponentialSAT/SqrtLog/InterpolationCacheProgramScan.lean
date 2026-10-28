import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramBasic

namespace OAI.Algorithms

/-! A fixed-width physical map scan. The service is an ordinary finite
subprogram, and its output is transferred into the actual packed table. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def mapStep (src dst arg : Fin 320) (service : Code) : Code :=
  take src arg ;; service ;; emit 208 dst ;; clear arg

def mapLoop (src dst arg : Fin 320) (service : Code) : Code :=
  .while 15 (mapStep src dst arg service ;; peek src)

def mapScan (src dst arg : Fin 320) (service : Code) : Code :=
  peek src ;; mapLoop src dst arg service

def MapPorts (src dst arg : Fin 320) : Prop :=
  Function.Injective (![104,270,271,src,dst,arg,208] : Fin 7 → Fin 320)

theorem peek_eval (s : Store) (r : Fin 16 → Bool) (src : Fin 320) :
    Eval (peek src) 1 (⟨r,s⟩ : Data) ⟨readRegs r 0 15 (s src).head?,s⟩ := by
  simpa [peek,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,
    execInstr,readRegs] using
    Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.peek src 0 15) (⟨r,s⟩ : Data))

theorem mapStep_run {C : Type*} (encode : C → List Bool) (f : C → C) (W K : ℕ)
    (hwidth : ∀x,(encode x).length=W) (src dst arg : Fin 320) (hp : MapPorts src dst arg)
    (service : Code) (P : Store → Prop)
    (stable : ∀s i v,P s → i∈([src,dst,arg,208] : List (Fin 320)) → P (Function.update s i v))
    (hspec : ∀s x,P s → s arg=encode x → s 208=[] →
      Runs service K s (Function.update s 208 (encode (f x))))
    (s : Store) (x : C) (rest : List Bool) (hP : P s)
    (hsrc : s src=encode x++rest) (harg : s arg=[]) (hresult : s 208=[])
    (h104 : (s 104).length=W) (h270 : s 270=[]) (h271 : s 271=[]) :
    Runs (mapStep src dst arg service) (K+19*W+17) s
      (Function.update (Function.update s src rest) dst ((encode (f x)).reverse++s dst)) := by
  have hsarg : src≠arg := hp.ne (by decide : (3:Fin 7)≠5)
  have hsd : src≠dst := hp.ne (by decide : (3:Fin 7)≠4)
  have hs208 : src≠208 := hp.ne (by decide : (3:Fin 7)≠6)
  have hdarg : dst≠arg := hp.ne (by decide : (4:Fin 7)≠5)
  have hd208 : dst≠208 := hp.ne (by decide : (4:Fin 7)≠6)
  have ha208 : arg≠208 := hp.ne (by decide : (5:Fin 7)≠6)
  have htake : Function.Injective (![104,270,271,src,arg] : Fin 5 → Fin 320) := by
    intro i j hij
    have hh : (![104,270,271,src,arg] : Fin 5 → Fin 320) =
        (![104,270,271,src,dst,arg,208] : Fin 7 → Fin 320) ∘
          (![0,1,2,3,5] : Fin 5 → Fin 7) := by funext k; fin_cases k <;> rfl
    rw [hh] at hij
    exact (by decide : Function.Injective (![0,1,2,3,5] : Fin 5 → Fin 7)) (hp hij)
  let s1 := Function.update (Function.update s src rest) arg (encode x)
  let s2 := Function.update s1 208 (encode (f x))
  let s3 := Function.update (Function.update s2 208 []) dst ((encode (f x)).reverse++s dst)
  have h1 : Runs (take src arg) (14*W+11) s s1 := by
    simpa only [s1,harg,List.append_nil,hwidth] using
      take_run s src arg htake (encode x) rest hsrc (h104.trans (hwidth x).symm) h270 h271
  have hP1 : P s1 := stable _ arg _ (stable _ src _ hP (by simp)) (by simp)
  have h2 : Runs service K s1 s2 := hspec s1 x hP1 (by simp [s1])
    (by simp [s1,Ne.symm ha208,Ne.symm hs208,hresult])
  have h3 : Runs (emit 208 dst) (3*W+3) s2 s3 := by
    simpa [s3,s2,s1,hd208,hdarg,Ne.symm hsd,hwidth] using emit_run s2 208 dst hd208.symm
  have h4 : Runs (clear arg) (2*W+3) s3 (Function.update s3 arg []) := by
    simpa [s3,s2,s1,ha208,Ne.symm hdarg,hwidth] using clear_run s3 arg
  have hout : Function.update s3 arg [] =
      Function.update (Function.update s src rest) dst ((encode (f x)).reverse++s dst) := by
    funext j
    by_cases ha : j=arg
    · subst j
      simp [s3,s2,s1,Ne.symm hdarg,Ne.symm hsarg,harg]
    · by_cases hr : j=208
      · subst j
        simp [s3,s2,s1,Ne.symm ha208,Ne.symm hd208,Ne.symm hs208,hresult]
      · simp [s3,s2,s1,Function.update_apply,ha,hr]
  have hh := h1.seq (h2.seq (h3.seq h4))
  rw [hout] at hh
  exact hh.mono (by omega)

/-- The scan preserves the full caller store except its consumed source and
its reverse accumulator. The output values are produced by the service. -/
theorem mapLoop_run {C : Type*} (encode : C → List Bool) (f : C → C) (W K : ℕ)
    (hW : 0 < W) (hwidth : ∀x,(encode x).length=W)
    (src dst arg : Fin 320) (hp : MapPorts src dst arg)
    (service : Code) (P : Store → Prop)
    (stable : ∀s i v,P s → i∈([src,dst,arg,208] : List (Fin 320)) → P (Function.update s i v))
    (hspec : ∀s x,P s → s arg=encode x → s 208=[] →
      Runs service K s (Function.update s 208 (encode (f x))))
    (s : Store) (xs : List C) (hP : P s) (hsrc : s src=xs.flatMap encode)
    (harg : s arg=[]) (hresult : s 208=[])
    (h104 : (s 104).length=W) (h270 : s 270=[]) (h271 : s 271=[])
    (r : Fin 16 → Bool) :
    ∃n rf,n ≤ xs.length*(K+19*W+19)+1 ∧
      Eval (mapLoop src dst arg service) n
        (⟨readRegs r 0 15 (s src).head?,s⟩ : Data)
        ⟨rf,Function.update (Function.update s src []) dst
          ((xs.flatMap fun x => encode (f x)).reverse++s dst)⟩ := by
  induction xs generalizing s r with
  | nil =>
      have hz : s src=[] := hsrc
      refine ⟨1,readRegs r 0 15 none,by simp,?_⟩
      have hu : Function.update s src []=s := by simpa only [hz] using Function.update_eq_self src s
      simp only [List.flatMap_nil,List.reverse_nil,List.nil_append,hu,Function.update_eq_self]
      simpa only [mapLoop, hz,List.head?_nil] using
        (Eval.while_false (body := mapStep src dst arg service ;; peek src)
          (a := (⟨readRegs r 0 15 none,s⟩ : Data)) (by simp [readRegs]))
  | cons x xs ih =>
      have hsarg : src≠arg := hp.ne (by decide : (3:Fin 7)≠5)
      have hsd : src≠dst := hp.ne (by decide : (3:Fin 7)≠4)
      have hs208 : src≠208 := hp.ne (by decide : (3:Fin 7)≠6)
      have hdarg : dst≠arg := hp.ne (by decide : (4:Fin 7)≠5)
      have hd208 : dst≠208 := hp.ne (by decide : (4:Fin 7)≠6)
      let mid := Function.update (Function.update s src (xs.flatMap encode)) dst
        ((encode (f x)).reverse++s dst)
      obtain ⟨n,rm,hn,he⟩ := mapStep_run encode f W K hwidth src dst arg hp service P stable hspec
        s x (xs.flatMap encode) hP hsrc harg hresult h104 h270 h271
        (readRegs r 0 15 (s src).head?)
      have hPm : P mid := stable _ dst _ (stable _ src _ hP (by simp)) (by simp)
      have hsm : mid src=xs.flatMap encode := by simp [mid,hsd]
      have ham : mid arg=[] := by simp [mid,Ne.symm hdarg,Ne.symm hsarg,harg]
      have hrm : mid 208=[] := by simp [mid,Ne.symm hd208,Ne.symm hs208,hresult]
      have hkeep (i : Fin 320) (hi : i=104 ∨ i=270 ∨ i=271) : mid i=s i := by
        rcases hi with rfl|rfl|rfl
        · simp only [mid,Function.update_of_ne (show (104:Fin 320)≠dst from hp.ne (by decide : (0:Fin 7)≠4)),Function.update_of_ne (show (104:Fin 320)≠src from hp.ne (by decide : (0:Fin 7)≠3))]
        · simp only [mid,Function.update_of_ne (show (270:Fin 320)≠dst from hp.ne (by decide : (1:Fin 7)≠4)),Function.update_of_ne (show (270:Fin 320)≠src from hp.ne (by decide : (1:Fin 7)≠3))]
        · simp only [mid,Function.update_of_ne (show (271:Fin 320)≠dst from hp.ne (by decide : (2:Fin 7)≠4)),Function.update_of_ne (show (271:Fin 320)≠src from hp.ne (by decide : (2:Fin 7)≠3))]
      obtain ⟨m,rf,hm,ht⟩ := ih mid hPm hsm ham hrm
        (by simpa only [hkeep 104 (by simp)] using h104)
        ((hkeep 270 (by simp)).trans h270) ((hkeep 271 (by simp)).trans h271) rm
      have hg : (readRegs r 0 15 (s src).head?) 15=true := by
        have he0 : encode x≠[] := fun hh => by have := hwidth x; simp [hh] at this; omega
        rw [hsrc,List.flatMap_cons]
        cases hh : encode x with
        | nil => exact (he0 hh).elim
        | cons b bs => simp [readRegs]
      have hloop := Eval.while_true hg (he.seq (peek_eval mid rm src)) ht
      refine ⟨n+1+m+1,rf,?_,?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · have hfinal : Function.update (Function.update mid src []) dst
            ((xs.flatMap fun x => encode (f x)).reverse++mid dst) =
            Function.update (Function.update s src []) dst
              (((x::xs).flatMap fun x => encode (f x)).reverse++s dst) := by
          funext i
          by_cases hi : i=dst
          · subst i; simp [mid,List.reverse_append,List.append_assoc]
          · by_cases hj : i=src
            · subst i; simp [mid,hsd]
            · simp [mid,hi,hj]
        rw [hfinal] at hloop
        exact hloop

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
