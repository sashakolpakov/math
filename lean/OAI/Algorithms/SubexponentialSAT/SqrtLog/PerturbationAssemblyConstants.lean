import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyControl
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramModel

namespace OAI.Algorithms

/-! Paid construction of the polynomial Horner point and seed. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor
open DensePolynomialProgram (Coeff)
open DensePolynomialProgram.Constructor

/-- Runtime theta209, full-ring one208, full-ring zero207 and jet count243. -/
def constructConstants : Code := .seq (construct 207 207 239)
  (.seq (construct 209 208 247) (copy 207 254))

def constantScratch : List (Fin 256) := [100,101,102,107,108,120,239,245,247,254]

def constantsState (s : Store) (J W : ℕ) : Store :=
  Function.update (Function.update (Function.update s
    239 (Counter.paddedBits W (s 207) (s 207) J))
    247 (Counter.paddedBits W (s 209) (s 208) J)) 254 (s 207)

theorem constructConstants_run (s : Store) (J W : ℕ)
    (hz : (s 207).length=W) (ho : (s 208).length=W) (hx : (s 209).length=W)
    (hJ : s 243=List.replicate J true) (h104 : s 104=List.replicate W false)
    (he : ∀ i ∈ constantScratch, s i=[]) :
    ExecutesIn constructConstants (440*(J+1)*(W+1)+7*W+5) s (constantsState s J W) := by
  let s1 := Function.update s 239 (Counter.paddedBits W (s 207) (s 207) J)
  let s2 := Function.update s1 247 (Counter.paddedBits W (s 209) (s 208) J)
  have h1 : ExecutesIn (construct 207 207 239) (220*(J+1)*(W+1)) s s1 := by
    apply DensePolynomialProgram.Constructor.construct_run
    all_goals first | decide | assumption | exact he _ (by simp [constantScratch])
  have h2 : ExecutesIn (construct 209 208 247) (220*(J+1)*(W+1)) s1 s2 := by
    apply DensePolynomialProgram.Constructor.construct_run
    all_goals first | decide | simpa [s1] using hx | simpa [s1] using ho |
      simpa [s1] using hJ | simpa [s1] using h104 |
      simpa [s1] using he _ (by simp [constantScratch])
  have h3 : ExecutesIn (copy 207 254) (7*W+5) s2 (constantsState s J W) := by
    simpa [s2,s1,constantsState,hz,he 254 (by simp [constantScratch])] using
      copy_run 207 254 s2 (by decide) (by decide) (by decide)
        (by simpa [s2,s1] using he 120 (by simp [constantScratch]))
  have hcost : 440*(J+1)*(W+1)+7*W+5 =
      220*(J+1)*(W+1)+(220*(J+1)*(W+1)+(7*W+5)) := by ring
  rw [hcost]
  exact h1.seq (h2.seq h3)

/-- Any protected cache can be replaced while its old value is preserved in a
fresh high backup port. Both copies are ordinary finite tape programs. -/
def saveReplace (src dst backup : Fin 256) : Code :=
  .seq (copy dst backup) (CRTLocalProgram.replace src dst)

theorem saveReplace_run (s : Store) (src dst backup : Fin 256)
    (hsd : src≠dst) (hsb : src≠backup) (hdb : dst≠backup)
    (hs : src≠120) (hd : dst≠120) (hb : backup≠120)
    (h120 : s 120=[]) (he : s backup=[]) :
    ExecutesIn (saveReplace src dst backup)
      (9*(s dst).length+7*(s src).length+13) s
      (Function.update (Function.update s backup (s dst)) dst (s src)) := by
  let s1 := Function.update s backup (s dst)
  have h1 : ExecutesIn (copy dst backup) (7*(s dst).length+5) s s1 := by
    simpa [s1,he] using copy_run dst backup s hdb hd (Ne.symm hb) h120
  have h2 : ExecutesIn (CRTLocalProgram.replace src dst)
      (2*(s dst).length+7*(s src).length+8) s1
      (Function.update s1 dst (s src)) := by
    simpa [s1,hsb,hdb] using CRTLocalProgram.replace_run s1 src dst hsd hs hd
      (by simpa [s1,Ne.symm hb] using h120)
  have hcost : 9*(s dst).length+7*(s src).length+13 =
      (7*(s dst).length+5)+(2*(s dst).length+7*(s src).length+8) := by omega
  rw [hcost]
  exact h1.seq h2

/-- Restoring a protected cache consumes the backup and clears the new value. -/
def restoreCache (dst backup : Fin 256) : Code := .seq (clear dst) (move backup dst)

theorem restoreCache_run (s : Store) (dst backup : Fin 256)
    (hdb : backup≠dst) (hd : dst≠245) (hb : backup≠245)
    (h245 : s 245=[]) :
    ExecutesIn (restoreCache dst backup)
      (2*(s dst).length+6*(s backup).length+9) s
      (Function.update (Function.update s backup []) dst (s backup)) := by
  have h1 := clear_run dst s
  have h2 := move_run (Function.update s dst []) backup dst hb hd hdb
    (by simpa [Ne.symm hd] using h245) (by simp)
  have hout : Function.update (Function.update (Function.update s dst []) backup []) dst
      ((Function.update s dst []) backup) =
      Function.update (Function.update s backup []) dst (s backup) := by
    funext i
    by_cases hi : i=dst <;> by_cases hj : i=backup <;>
      simp [hi,hj,hdb]
  rw [hout] at h2
  have h := h1.seq h2
  have hbackup : (Function.update s dst [] backup).length = (s backup).length := by
    rw [Function.update_noteq hdb]
  have hcost : 2*(s dst).length+6*(s backup).length+9 =
      (2*(s dst).length+3)+(6*(Function.update s dst [] backup).length+6) := by
    rw [hbackup]
    omega
  rw [hcost]
  exact h

/-- Bit-level point construction agrees with the fixed-array model. -/
theorem point_bits {B d : ℕ} (z one theta : Coeff B d)
    (hz : RingProgram.flat z=List.replicate (d*B) false) (J : ℕ) :
    Counter.paddedBits (d*B) (RingProgram.flat theta) (RingProgram.flat one) J =
      DensePolynomialProgram.Fixed.encode (CRTLocalProgram.Model.linear z one theta J) :=
  (CRTLocalProgram.Model.padded_encode z theta one hz J).symm

theorem zero_coefficients {C : Type*} (z : C) (J : ℕ) :
    DensePolynomialProgram.Constructor.coefficients z z z J=List.replicate J z := by
  cases J with
  | zero => rfl
  | succ J => cases J <;> simp [DensePolynomialProgram.Constructor.coefficients,List.replicate_succ]

theorem zero_bits {B d : ℕ} (z : Coeff B d)
    (hz : RingProgram.flat z=List.replicate (d*B) false) (J : ℕ) :
    Counter.paddedBits (d*B) (RingProgram.flat z) (RingProgram.flat z) J =
      DensePolynomialProgram.Fixed.encode (CRTLocalProgram.Model.zero z J) := by
  rw [← DensePolynomialProgram.Constructor.encode_coefficients z z z hz J,zero_coefficients]
  rfl

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
