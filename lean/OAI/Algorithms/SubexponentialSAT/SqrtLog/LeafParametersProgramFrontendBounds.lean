import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramFrontendPoly
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramExports
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramIntervalBounds

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual parameter/export prefix. Only
input counts and input word lengths enter the final bound. In particular the
large grid value never becomes a unary counter in this prefix. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod



def smallPorts : List (Fin 64) := [0,5,18,21,29]
def resultPorts : List (Fin 64) := [0,5,18,21,29,46,47,50]

def preHeight (B : ℕ) := iterMajorant Interval.prepare.length (B+2)
def widthInput (B : ℕ) := preHeight B+16*(B+1)
def widthHeight (B : ℕ) := iterMajorant CacheWidth.code.length (widthInput B)
def valueHeight (B : ℕ) := 4*(B+1)^2
def height (B : ℕ) := preHeight B+widthHeight B+valueHeight B+B+1

theorem height_ge (B : ℕ) :
    1 ≤ height B ∧ B ≤ height B ∧ preHeight B ≤ height B ∧
    widthHeight B ≤ height B ∧ valueHeight B ≤ height B := by dsimp [height]; omega

theorem prepare_scale (B : ℕ) (m : Model) : ScaleBound (B+2) Interval.prepare m := by
  simp [Interval.prepare,ScaleBound,scale]

theorem interval_bounds (m : Model) (B : ℕ) (hl : ∀ j,m.len j ≤ B) :
    (∀ j,(Interval.finalModel m).len j ≤ widthHeight B) ∧
    Interval.runtimeBound m ≤ Interval.prepare.length*preHeight B+
      10000*(3*B+1)^2+1+CacheWidth.code.length*widthHeight B := by
  have hpre := budget_majorant Interval.prepare m (B+2)
    (fun j => (hl j).trans (by omega)) (prepare_scale B m)
  have hint : ∀ j,(Interval.intervalModel m).len j ≤ widthInput B := by
    intro j
    by_cases hj : j=46
    · subst j
      simp only [Interval.intervalModel,Function.update_self]
      have h1 := hl 18
      have h2 := hl 21
      have h3 := hl 29
      dsimp [widthInput]
      omega
    · simp only [Interval.intervalModel,Function.update_of_ne hj]
      exact (hpre.1 j).trans (by dsimp [preHeight,widthInput]; omega)
  have hwidth : 2 ≤ widthInput B := by dsimp [widthInput]; omega
  have hw := budget_majorant CacheWidth.code (Interval.intervalModel m) (widthInput B) hint
    (scaleBound_mono 2 _ hwidth _ _ (CacheWidth.scaleBound _))
  refine ⟨hw.1,?_⟩
  have hsum : m.len 18+m.len 21+m.len 29+1 ≤ 3*B+1 := by
    have := hl 18; have := hl 21; have := hl 29; omega
  unfold Interval.runtimeBound
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hpre.2
    (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hsum 2))) le_rfl) hw.2

theorem interval_values (m : Model) (B : ℕ)
    (hv : ∀ j∈smallPorts,m.val j ≤ B) (hr : 0 < m.val 18) :
    ∀ j∈resultPorts,(Interval.finalModel m).val j ≤ valueHeight B := by
  have h0 := hv 0 (by simp [smallPorts])
  have h5 := hv 5 (by simp [smallPorts])
  have hrB := hv 18 (by simp [smallPorts])
  have hQB := hv 21 (by simp [smallPorts])
  have hRB := hv 29 (by simp [smallPorts])
  have hA := (Interval.intervalStart_le_Q (m.val 18) (m.val 21) (m.val 29) hr).trans hQB
  have hvals := Interval.final_values m
  have hB : B ≤ valueHeight B := by dsimp [valueHeight]; nlinarith
  have hQr : m.val 21*m.val 18 ≤ valueHeight B := by
    have hh := Nat.mul_le_mul hQB hrB
    dsimp [valueHeight]
    nlinarith
  have hW : 1+2*Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29)*m.val 29+m.val 21 ≤ valueHeight B := by
    have hh := Nat.mul_le_mul hA hRB
    dsimp [valueHeight]
    nlinarith
  intro j hj
  simp only [resultPorts,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [(Exports.intervalModel_frame m 0 (by decide)).1]; exact h0.trans hB
  · rw [(Exports.intervalModel_frame m 5 (by decide)).1]; exact h5.trans hB
  · rw [(Exports.intervalModel_frame m 18 (by decide)).1]; exact hrB.trans hB
  · rw [(Exports.intervalModel_frame m 21 (by decide)).1]; exact hQB.trans hB
  · rw [hvals.1]; exact hRB.trans hB
  · rw [hvals.2.1]; exact hA.trans hB
  · rw [hvals.2.2.1]; exact hQr
  · rw [hvals.2.2.2]; exact hW

theorem unaryBound_mono (v l H : ℕ) (hv : v ≤ H) (hl : l ≤ H) :
    Cache.unaryBound v l ≤ Cache.unaryBound H H := by unfold Cache.unaryBound; gcongr

theorem unaryBound_square (H : ℕ) (hH : 1 ≤ H) : Cache.unaryBound H H ≤ 141*H^2 := by
  have hsq : H ≤ H^2 := by nlinarith
  dsimp [Cache.unaryBound]
  nlinarith

theorem cacheLength_bound (m : Model) (H : ℕ) (hl : ∀ j,m.len j ≤ H)
    (hv : ∀ j∈resultPorts,m.val j ≤ H) (j : Fin 64) : Exports.cacheLength m j ≤ H := by
  unfold Exports.cacheLength
  split_ifs
  · exact hv 50 (by simp [resultPorts])
  · exact hv 46 (by simp [resultPorts])
  · exact hv 29 (by simp [resultPorts])
  · exact hl j

theorem tail_bounds (m : Model) (H : ℕ) (hl : ∀ j,m.len j ≤ H)
    (hv : ∀ j∈resultPorts,m.val j ≤ H) :
    Cache.unaryRuntime m ≤ 3*Cache.unaryBound H H ∧
    Exports.exportModelBudget m ≤ 16*Cache.unaryBound H H ∧
    Exports.clearModelBudget m ≤ 36*H+57 := by
  have hu (j : Fin 64) (hj : j∈resultPorts) :
      Cache.unaryBound (m.val j) (m.len j) ≤ Cache.unaryBound H H :=
    unaryBound_mono _ _ _ (hv j hj) (hl j)
  constructor
  · have h29 := hu 29 (by simp [resultPorts])
    have h46 := hu 46 (by simp [resultPorts])
    have h50 := hu 50 (by simp [resultPorts])
    dsimp [Cache.unaryRuntime]
    omega
  constructor
  · have hf : ∀ i : Fin 16,Exports.exportFieldBound m i ≤ Cache.unaryBound H H := by
      intro i
      unfold Exports.exportFieldBound
      split_ifs with hi
      · apply hu
        fin_cases i <;> simp_all [Exports.localSource,resultPorts]
      · have hc := cacheLength_bound m H hl hv (Exports.localSource i)
        dsimp [Cache.unaryBound]
        omega
    have hh := List.sum_le_sum (l := List.finRange 16)
      (f := Exports.exportFieldBound m) (g := fun _ => Cache.unaryBound H H) (fun i _ => hf i)
    change (List.finRange 16 |>.map (Exports.exportFieldBound m)).sum ≤
      16 * Cache.unaryBound H H
    exact hh.trans_eq (by simp; omega)
  · have hh := List.sum_le_sum (l := List.finRange 18)
      (f := fun i => Exports.cacheLength m ⟨46+i.val,by omega⟩) (g := fun _ => H)
      (fun i _ => cacheLength_bound m H hl hv _)
    have hs : ((List.finRange 18).map (fun i => Exports.cacheLength m ⟨46+i.val,by omega⟩)).sum ≤ 18*H := by
      exact hh.trans_eq (by simp; omega)
    dsimp [Exports.clearModelBudget]
    omega

/-- A concrete fixed polynomial majorant expressed using two fixed iterates
of the already certified arithmetic-table majorant. -/
def postMajorant (B : ℕ) : ℕ := 200000*(height B)^2

theorem prepareBudget_bound (m : Model) (B : ℕ) (hl : ∀ j,m.len j ≤ B)
    (hv : ∀ j∈smallPorts,m.val j ≤ B) (hr : 0 < m.val 18) :
    Exports.prepareBudget m ≤ postMajorant B := by
  obtain ⟨hH,hBH,hpreH,hwH,hvH⟩ := height_ge B
  obtain ⟨hlf,hint⟩ := interval_bounds m B hl
  have hvf := interval_values m B hv hr
  obtain ⟨hu,he,hc⟩ := tail_bounds (Interval.finalModel m) (height B)
    (fun j => (hlf j).trans hwH) (fun j hj => (hvf j hj).trans hvH)
  have hsquare := unaryBound_square (height B) hH
  have hsq : height B ≤ (height B)^2 := by nlinarith
  have hroot : (3*B+1)^2 ≤ 16*(height B)^2 := by
    calc
      _ ≤ (4*height B)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have hint' : Interval.runtimeBound m ≤ 160028*(height B)^2 := by
    have hpre : Interval.prepare.length=18 := by rfl
    have hw : CacheWidth.code.length=9 := by rfl
    rw [hpre,hw] at hint
    nlinarith
  unfold Exports.prepareBudget Cache.runtimeBound postMajorant
  nlinarith

theorem postMajorant_poly : Poly (fun B => B+1) postMajorant := by
  have hmeasure : ∀ B : ℕ,1 ≤ B+1 := by omega
  have hp0 : Poly (fun B => B+1) preHeight :=
    Poly.iter (Poly.add hmeasure (Poly.self _) (Poly.const _ 1))
      (by intro B; omega) Interval.prepare.length
  have hp1 : Poly (fun B => B+1) widthInput :=
    Poly.add hmeasure hp0 (Poly.mul (Poly.const _ 16) (Poly.self _))
  have hp2 : Poly (fun B => B+1) widthHeight :=
    Poly.iter hp1 (by intro B; dsimp [widthInput]; omega) CacheWidth.code.length
  have hpv : Poly (fun B => B+1) valueHeight :=
    Poly.mul (Poly.const _ 4) (Poly.pow (Poly.self _) 2)
  have hpid : Poly (fun B => B+1) (fun B => B) := (Poly.self _).mono (by intro B; omega)
  have hh : Poly (fun B => B+1) height :=
    Poly.add hmeasure (Poly.add hmeasure (Poly.add hmeasure (Poly.add hmeasure hp0 hp2) hpv) hpid)
      (Poly.const _ 1)
  exact Poly.mul (Poly.const _ 200000) (Poly.pow hh 2)

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
