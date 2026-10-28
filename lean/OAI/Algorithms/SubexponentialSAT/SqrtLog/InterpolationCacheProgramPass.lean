import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgramScan

namespace OAI.Algorithms

/-! Packed scans starting from a preserved node master. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem mapScan_run {C : Type*} (encode : C → List Bool) (f : C → C) (W K : ℕ)
    (hW : 0 < W) (hwidth : ∀x,(encode x).length=W)
    (src dst arg : Fin 320) (hp : MapPorts src dst arg)
    (service : Code) (P : Store → Prop)
    (stable : ∀s i v,P s → i∈([src,dst,arg,208] : List (Fin 320)) → P (Function.update s i v))
    (hspec : ∀s x,P s → s arg=encode x → s 208=[] →
      Runs service K s (Function.update s 208 (encode (f x))))
    (s : Store) (xs : List C) (hP : P s) (hsrc : s src=xs.flatMap encode)
    (harg : s arg=[]) (hresult : s 208=[])
    (h104 : (s 104).length=W) (h270 : s 270=[]) (h271 : s 271=[]) :
    Runs (mapScan src dst arg service) (xs.length*(K+19*W+19)+2) s
      (Function.update (Function.update s src []) dst
        ((xs.flatMap fun x => encode (f x)).reverse++s dst)) := by
  intro r
  obtain ⟨n,rf,hn,he⟩ := mapLoop_run encode f W K hW hwidth src dst arg hp service P stable
    hspec s xs hP hsrc harg hresult h104 h270 h271 r
  exact ⟨1+n,rf,by omega,(peek_eval s r src).seq he⟩

def scanMaster (src dst arg : Fin 320) (service : Code) : Code :=
  .seq (copy 256 src) (mapScan src dst arg service)

theorem flatMap_length {C : Type*} (encode : C → List Bool) (W : ℕ)
    (hwidth : ∀x,(encode x).length=W) (xs : List C) :
    (xs.flatMap encode).length=xs.length*W := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,hwidth,Nat.add_mul,Nat.add_comm]

theorem scanMaster_run {C : Type*} (encode : C → List Bool) (f : C → C) (W K : ℕ)
    (hW : 0 < W) (hwidth : ∀x,(encode x).length=W)
    (src dst arg : Fin 320) (hp : MapPorts src dst arg) (h256 : (256:Fin 320)≠src)
    (service : Code) (P : Store → Prop)
    (stable : ∀s i v,P s → i∈([src,dst,arg,208] : List (Fin 320)) → P (Function.update s i v))
    (hspec : ∀s x,P s → s arg=encode x → s 208=[] →
      Runs service K s (Function.update s 208 (encode (f x))))
    (s : Store) (xs : List C) (hP : P s) (hmaster : s 256=xs.flatMap encode)
    (hsrc : s src=[]) (harg : s arg=[]) (hresult : s 208=[])
    (h104 : (s 104).length=W) (h270 : s 270=[]) (h271 : s 271=[]) :
    Runs (scanMaster src dst arg service) (xs.length*(K+26*W+19)+7) s
      (Function.update s dst ((xs.flatMap fun x => encode (f x)).reverse++s dst)) := by
  have hs270 : (270:Fin 320)≠src := hp.ne (by decide : (1:Fin 7)≠3)
  let mid := Function.update s src (xs.flatMap encode)
  have h1 : Runs (copy 256 src) (7*(xs.length*W)+5) s mid := by
    simpa only [mid,hmaster,hsrc,List.append_nil,flatMap_length encode W hwidth] using
      copy_run s 256 src h256 (by decide) hs270 h270
  have h2 := mapScan_run encode f W K hW hwidth src dst arg hp service P stable hspec mid xs
    (stable _ src _ hP (by simp)) (by simp [mid])
    (by simp [mid,(show arg≠src from hp.ne (by decide : (5:Fin 7)≠3)),harg])
    (by simp [mid,(show (208:Fin 320)≠src from hp.ne (by decide : (6:Fin 7)≠3)),hresult])
    (by simpa only [mid,Function.update_of_ne ((show (104:Fin 320)≠src from hp.ne (by decide : (0:Fin 7)≠3)))] using h104)
    (by simpa only [mid,Function.update_of_ne hs270] using h270)
    (by simpa only [mid,Function.update_of_ne ((show (271:Fin 320)≠src from hp.ne (by decide : (2:Fin 7)≠3)))] using h271)
  have hend : Function.update (Function.update mid src []) dst
      ((xs.flatMap fun x => encode (f x)).reverse++mid dst) =
      Function.update s dst ((xs.flatMap fun x => encode (f x)).reverse++s dst) := by
    simp only [mid,Function.update_idem,Function.update_of_ne (show dst≠src from hp.ne (by decide : (4:Fin 7)≠3))]
    rw [←hsrc,Function.update_eq_self]
  rw [hend] at h2
  exact (h1.seq h2).mono (by nlinarith)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
