import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialHornerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalConstantProgram

namespace OAI.Algorithms

/-! Actual local inverse-series preparation and evaluation. All arithmetic
is delegated to fixed, proved bit programs; the hypotheses describe only
the stored arrays and the arithmetic workspace. -/

namespace SubexponentialSAT.SubexpLocalGeometricProgram

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def prepareDefect : Code :=
  copy 228 241 ;; SubexpPolynomialHornerProgram.multiply ;;
    SubexpPolynomialHornerProgram.addOne ;; copy 240 222 ;; clear 240 ;;
    copy 242 240 ;; copy 222 241

def series : Code :=
  SubexpLocalConstantProgram.seriesCounter ;; SubexpPolynomialHornerProgram.command

def inverse : Code :=
  series ;; clear 241 ;; copy 227 241 ;; SubexpPolynomialHornerProgram.multiply

def correction : Code :=
  clear 241 ;; copy 225 241 ;; SubexpPolynomialMultiplyService.command

def command : Code := prepareDefect ;; inverse ;; correction

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D

structure Ready (s : Store) (t : Coeff p D) (width : List Bool)
    (frame : Fin 6 → List Bool) : Prop where
  multiply : SubexpConvolutionPairSpec.BaseReady p (D + 1) M s t width frame
  add : ∀ i, s (SubexpPolynomialAddService.ports i) =
    (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i
  buffers : ∀ i, s (bufferPorts i) = []
  scratch : ∀ i ∈ ([120,121,122,244,245] : List (Fin 256)), s i = []

omit [Fact p.Prime] in
theorem ready_congr (s s' : Store) (t : Coeff p D) (width : List Bool)
    (frame : Fin 6 → List Bool) (H : Ready p D M s t width frame)
    (h : ∀ j : Fin 256, j.val < 205 → s' j = s j)
    (h244 : s' 244 = s 244) (h245 : s' 245 = s 245) :
    Ready p D M s' t width frame := by
  constructor
  · exact baseReady_congr p (D + 1) M s s' t width frame h H.multiply
  · intro i
    rw [h _ (by
      dsimp [SubexpPolynomialAddService.ports]
      have := i.isLt
      omega)]
    exact H.add i
  · intro i
    rw [h _ (bufferPorts_lt i)]
    exact H.buffers i
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · rw [h 120 (by decide)]; exact H.scratch 120 (by decide)
    · rw [h 121 (by decide)]; exact H.scratch 121 (by decide)
    · rw [h 122 (by decide)]; exact H.scratch 122 (by decide)
    · rw [h244]; exact H.scratch 244 (by decide)
    · rw [h245]; exact H.scratch 245 (by decide)

omit [Fact p.Prime] in
theorem ready_update (s : Store) (t : Coeff p D) (width : List Bool)
    (frame : Fin 6 → List Bool) (H : Ready p D M s t width frame)
    (j : Fin 256) (x : List Bool) (hj : 205 ≤ j.val) (h244 : j ≠ 244) (h245 : j ≠ 245) :
    Ready p D M (Function.update s j x) t width frame := by
  apply ready_congr p D M s _ t width frame H
  · intro i hi
    have hij : i ≠ j := by intro he; subst i; omega
    simp [hij]
  · simp [Ne.symm h244]
  · simp [Ne.symm h245]

theorem multiply_value (s : Store) (t z : Coeff p D) (P Q : Poly p D)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : Ready p D M s t width frame)
    (hleft : s 240 = encode p (D + 1) P)
    (hright : s 241 = encode p (D + 1) Q)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) :
    ExecutesIn SubexpPolynomialHornerProgram.multiply
      (602000 * (D + 1)^3 * (baseWidth p (D + 1) + 1)^2) s
      (Function.update s 240 (encode p (D + 1) (next p (D + 1) M t z Q P))) := by
  have hm := SubexpPolynomialMultiplyService.command_value p (D + 1) M s t z width frame
    H.multiply H.buffers (H.scratch 120 (by decide)) (H.scratch 121 (by decide))
    (H.scratch 122 (by decide)) (H.scratch 244 (by decide)) (H.scratch 245 (by decide))
    D P.val Q.val P.property Q.property hleft hright hzero hD
  have hc := SubexpPolynomialIterationControl.step_run SubexpPolynomialMultiplyService.command
    (601000 * (D + 1)^3 * (baseWidth p (D + 1) + 1)^2) s
    (encode p (D + 1) (next p (D + 1) M t z Q P))
    (H.scratch 244 (by decide)) (H.scratch 245 (by decide)) hm
  apply hc.mono
  rw [hleft, encode_length, encode_length]
  ring_nf
  omega

def defect (t z o : Coeff p D) (P N O : Poly p D) : Poly p D :=
  SubexpPolynomialHornerProgram.sum p D M t z o (next p (D + 1) M t z N P) O

def defectState (s : Store) (t z o : Coeff p D) (P N O Z : Poly p D) : Store :=
  Function.update (Function.update (Function.update s
    222 (encode p (D + 1) (defect p D M t z o P N O)))
    240 (encode p (D + 1) Z))
    241 (encode p (D + 1) (defect p D M t z o P N O))

theorem prepareDefect_value (s : Store) (t z o : Coeff p D) (P N O Z : Poly p D)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : Ready p D M s t width frame)
    (hleft : s 240 = encode p (D + 1) P)
    (hnegative : s 228 = encode p (D + 1) N)
    (hone : s 220 = encode p (D + 1) O)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hzero' : s 242 = encode p (D + 1) Z)
    (hD : (s 243).length = D) (h222 : s 222 = []) (h241 : s 241 = []) :
    ExecutesIn prepareDefect
      (670000 * (D + 1)^3 * (baseWidth p (D + 1) + 1)^2) s
      (defectState p D M s t z o P N O Z) := by
  let B := baseWidth p (D + 1)
  let R := next p (D + 1) M t z N P
  let F := defect p D M t z o P N O
  let s₁ := Function.update s 241 (encode p (D + 1) N)
  let s₂ := Function.update s₁ 240 (encode p (D + 1) R)
  let s₃ := Function.update (Function.update s 240 (encode p (D + 1) F)) 241 []
  let s₄ := Function.update s₃ 222 (encode p (D + 1) F)
  let s₅ := Function.update s₄ 240 []
  let s₆ := Function.update s₄ 240 (encode p (D + 1) Z)
  have H₁ : Ready p D M s₁ t width frame :=
    ready_update p D M s t width frame H 241 _ (by decide) (by decide) (by decide)
  have H₂ : Ready p D M s₂ t width frame :=
    ready_update p D M s₁ t width frame H₁ 240 _ (by decide) (by decide) (by decide)
  have h₁ : ExecutesIn (copy 228 241) (28 * D * B + 5) s s₁ := by
    have h := copy_run 228 241 s (by decide) (by decide) (by decide) (H.scratch 120 (by decide))
    convert h using 1
    all_goals simp [s₁, hnegative, h241, encode_length, B]
    all_goals ring
  have h₂ : ExecutesIn SubexpPolynomialHornerProgram.multiply
      (602000 * (D + 1)^3 * (B + 1)^2) s₁ s₂ :=
    multiply_value p D M s₁ t z P N width frame H₁
      (by simp [s₁, hleft]) (by simp [s₁]) (by simp [s₁, hzero]) (by simp [s₁, hD])
  have he₃ : Function.update (Function.update s₂ 240 (encode p (D + 1) F)) 241 [] = s₃ := by
    funext i
    by_cases hi : i = 241 <;> by_cases h240 : i = 240 <;>
      simp [s₃, s₂, s₁, hi, h240]
  have h₃ : ExecutesIn SubexpPolynomialHornerProgram.addOne
      (64000 * (D + 1) * (B + 1)^2) s₂ s₃ := by
    have h := SubexpPolynomialHornerProgram.addOne_value p D M t z o s₂ R N O
      width frame H₂.multiply.scalarWidthLength H₂.add
      (H₂.scratch 120 (by decide)) (H₂.scratch 244 (by decide)) (H₂.scratch 245 (by decide))
      (by simp [s₂]) (by simp [s₂, s₁]) (by simp [s₂, s₁, hone])
    change ExecutesIn _ _ s₂
      (Function.update (Function.update s₂ 240 (encode p (D + 1) F)) 241 []) at h
    rw [he₃] at h
    exact h
  have h₄ : ExecutesIn (copy 240 222) (28 * D * B + 5) s₃ s₄ := by
    have h := copy_run 240 222 s₃ (by decide) (by decide) (by decide)
      (by simp [s₃, H.scratch 120 (by decide)])
    convert h using 1
    all_goals simp [s₄, s₃, h222, encode_length, B]
    all_goals ring
  have h₅ : ExecutesIn (clear 240) (8 * D * B + 3) s₄ s₅ := by
    convert clear_run 240 s₄ using 1
    all_goals simp [s₄, s₃, encode_length, B]
    all_goals ring
  have h₆ : ExecutesIn (copy 242 240) (28 * D * B + 5) s₅ s₆ := by
    have h := copy_run 242 240 s₅ (by decide) (by decide) (by decide)
      (by simp [s₅, s₄, s₃, H.scratch 120 (by decide)])
    convert h using 1
    all_goals simp [s₆, s₅, s₄, s₃, hzero', encode_length, B]
    all_goals ring
  have he₇ : Function.update s₆ 241 (s₆ 222 ++ s₆ 241) = defectState p D M s t z o P N O Z := by
    funext i
    by_cases h241' : i = 241 <;> by_cases h240' : i = 240 <;> by_cases h222' : i = 222 <;>
      simp [s₆, s₄, s₃, defectState, F, h241', h240', h222']
  have h₇ : ExecutesIn (copy 222 241) (28 * D * B + 5) s₆
      (defectState p D M s t z o P N O Z) := by
    have h := copy_run 222 241 s₆ (by decide) (by decide) (by decide)
      (by simp [s₆, s₄, s₃, H.scratch 120 (by decide)])
    rw [he₇] at h
    convert h using 1
    all_goals simp [s₆, s₄, encode_length, B]
    all_goals ring
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq (h₆.seq h₇)))))
  apply h.mono
  dsimp only [B]
  ring_nf
  omega

def seriesValue (t z o : Coeff p D) (F O Z : Poly p D) : Poly p D :=
  ((SubexpPolynomialHornerProgram.value p D M t z o F O)^[D + (D + 1)]) Z

theorem series_value (s : Store) (t z o : Coeff p D) (F O Z : Poly p D)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : Ready p D M s t width frame)
    (hleft : s 240 = encode p (D + 1) Z)
    (hright : s 241 = encode p (D + 1) F)
    (hone : s 220 = encode p (D + 1) O)
    (hdefect : s 222 = encode p (D + 1) F)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : s 243 = List.replicate D true) (h246 : s 246 = []) :
    ExecutesIn series
      (1500000 * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2) s
      (Function.update s 240 (encode p (D + 1) (seriesValue p D M t z o F O Z))) := by
  let count := List.replicate (D + (D + 1)) true
  let s₁ := Function.update s 246 count
  let R := seriesValue p D M t z o F O Z
  have h₁ : ExecutesIn SubexpLocalConstantProgram.seriesCounter (14 * D + 12) s s₁ :=
    SubexpLocalConstantProgram.seriesCounter_run s D hD h246 (H.scratch 120 (by decide))
  have h₂ := SubexpPolynomialHornerProgram.command_value p D M t z o s F O Z count
    width frame H.multiply H.add H.buffers (H.scratch 120 (by decide))
    (H.scratch 121 (by decide)) (H.scratch 122 (by decide))
    (H.scratch 244 (by decide)) (H.scratch 245 (by decide))
    hright hone hdefect hzero (by simp [hD])
  have hstart : SubexpPolynomialIterationControl.ready s (encode p (D + 1)) Z count = s₁ := by
    funext i
    by_cases hi : i = 246 <;> by_cases h240 : i = 240 <;>
      simp [s₁, SubexpPolynomialIterationControl.ready, hi, h240, hleft]
  have hfinish : SubexpPolynomialIterationControl.ready s (encode p (D + 1)) R [] =
      Function.update s 240 (encode p (D + 1) R) := by
    funext i
    by_cases hi : i = 246 <;> by_cases h240 : i = 240 <;>
      simp [SubexpPolynomialIterationControl.ready, hi, h240, h246]
  simp only [count, List.length_replicate] at h₂
  change ExecutesIn _ _ _ (SubexpPolynomialIterationControl.ready s (encode p (D + 1)) R []) at h₂
  rw [hstart, hfinish] at h₂
  have h := h₁.seq h₂
  apply h.mono
  ring_nf
  omega

def inverseValue (t z o : Coeff p D) (F O Z Cb : Poly p D) : Poly p D :=
  next p (D + 1) M t z Cb (seriesValue p D M t z o F O Z)

theorem inverse_value (s : Store) (t z o : Coeff p D) (F O Z Cb : Poly p D)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : Ready p D M s t width frame)
    (hleft : s 240 = encode p (D + 1) Z)
    (hright : s 241 = encode p (D + 1) F)
    (hone : s 220 = encode p (D + 1) O)
    (hdefect : s 222 = encode p (D + 1) F)
    (hseed : s 227 = encode p (D + 1) Cb)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : s 243 = List.replicate D true) (h246 : s 246 = []) :
    ExecutesIn inverse
      (2200000 * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2) s
      (Function.update (Function.update s 240
        (encode p (D + 1) (inverseValue p D M t z o F O Z Cb)))
        241 (encode p (D + 1) Cb)) := by
  let B := baseWidth p (D + 1)
  let R := seriesValue p D M t z o F O Z
  let I := inverseValue p D M t z o F O Z Cb
  let s₁ := Function.update s 240 (encode p (D + 1) R)
  let s₂ := Function.update s₁ 241 []
  let s₃ := Function.update s₁ 241 (encode p (D + 1) Cb)
  have h₁ : ExecutesIn series (1500000 * (D + 1)^4 * (B + 1)^2) s s₁ :=
    series_value p D M s t z o F O Z width frame H hleft hright hone hdefect hzero hD h246
  have h₂ : ExecutesIn (clear 241) (8 * D * B + 3) s₁ s₂ := by
    convert clear_run 241 s₁ using 1
    all_goals simp [s₁, hright, encode_length, B]
    all_goals ring
  have h₃ : ExecutesIn (copy 227 241) (28 * D * B + 5) s₂ s₃ := by
    have h := copy_run 227 241 s₂ (by decide) (by decide) (by decide)
      (by simp [s₂, s₁, H.scratch 120 (by decide)])
    convert h using 1
    all_goals simp [s₃, s₂, s₁, hseed, encode_length, B]
    all_goals ring
  have H₁ : Ready p D M s₁ t width frame :=
    ready_update p D M s t width frame H 240 _ (by decide) (by decide) (by decide)
  have H₃ : Ready p D M s₃ t width frame :=
    ready_update p D M s₁ t width frame H₁ 241 _ (by decide) (by decide) (by decide)
  have he : Function.update s₃ 240 (encode p (D + 1) I) =
      Function.update (Function.update s 240 (encode p (D + 1) I))
        241 (encode p (D + 1) Cb) := by
    funext i
    by_cases hi : i = 241 <;> by_cases h240 : i = 240 <;>
      simp [s₃, s₁, hi, h240]
  have h₄ : ExecutesIn SubexpPolynomialHornerProgram.multiply
      (602000 * (D + 1)^3 * (B + 1)^2) s₃
      (Function.update (Function.update s 240 (encode p (D + 1) I))
        241 (encode p (D + 1) Cb)) := by
    have h := multiply_value p D M s₃ t z R Cb width frame H₃
      (by simp [s₃, s₁]) (by simp [s₃]) (by simp [s₃, s₁, hzero])
      (by simp [s₃, s₁, hD])
    change ExecutesIn _ _ s₃ (Function.update s₃ 240 (encode p (D + 1) I)) at h
    rw [he] at h
    exact h
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  apply h.mono
  dsimp only [B]
  ring_nf
  omega

theorem correction_value (s : Store) (t z : Coeff p D) (I Cb J : Poly p D)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : Ready p D M s t width frame)
    (hleft : s 240 = encode p (D + 1) I)
    (hright : s 241 = encode p (D + 1) Cb)
    (hjet : s 225 = encode p (D + 1) J)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) :
    ExecutesIn correction
      (602000 * (D + 1)^3 * (baseWidth p (D + 1) + 1)^2) s
      (Function.update (Function.update s 241 (encode p (D + 1) J))
        244 (encode p (D + 1) (next p (D + 1) M t z J I))) := by
  let B := baseWidth p (D + 1)
  let s₁ := Function.update s 241 []
  let s₂ := Function.update s 241 (encode p (D + 1) J)
  have h₁ : ExecutesIn (clear 241) (8 * D * B + 3) s s₁ := by
    convert clear_run 241 s using 1
    all_goals simp [hright, encode_length, B]
    all_goals ring
  have h₂ : ExecutesIn (copy 225 241) (28 * D * B + 5) s₁ s₂ := by
    have h := copy_run 225 241 s₁ (by decide) (by decide) (by decide)
      (by simp [s₁, H.scratch 120 (by decide)])
    convert h using 1
    all_goals simp [s₂, s₁, hjet, encode_length, B]
    all_goals ring
  have H₂ : Ready p D M s₂ t width frame :=
    ready_update p D M s t width frame H 241 _ (by decide) (by decide) (by decide)
  have h₃ := SubexpPolynomialMultiplyService.command_value p (D + 1) M s₂ t z width frame
    H₂.multiply H₂.buffers (H₂.scratch 120 (by decide)) (H₂.scratch 121 (by decide))
    (H₂.scratch 122 (by decide)) (H₂.scratch 244 (by decide)) (H₂.scratch 245 (by decide))
    D I.val J.val I.property J.property (by simp [s₂, hleft, encode]) (by simp [s₂, encode])
    (by simp [s₂, hzero]) (by simp [s₂, hD])
  have h := h₁.seq (h₂.seq h₃)
  apply h.mono
  dsimp only [B]
  ring_nf
  omega

def output (s : Store) (t z o : Coeff p D) (P N Cb O Z J : Poly p D) : Store :=
  let F := defect p D M t z o P N O
  let I := inverseValue p D M t z o F O Z Cb
  Function.update (Function.update (Function.update (Function.update s
    222 (encode p (D + 1) F)) 240 (encode p (D + 1) I)) 241 (encode p (D + 1) J))
    244 (encode p (D + 1) (next p (D + 1) M t z J I))

theorem command_value (s : Store) (t z o : Coeff p D) (P N Cb O Z J : Poly p D)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : Ready p D M s t width frame)
    (hleft : s 240 = encode p (D + 1) P)
    (hnegative : s 228 = encode p (D + 1) N)
    (hseed : s 227 = encode p (D + 1) Cb)
    (hone : s 220 = encode p (D + 1) O)
    (hjet : s 225 = encode p (D + 1) J)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hzero' : s 242 = encode p (D + 1) Z)
    (hD : s 243 = List.replicate D true)
    (h222 : s 222 = []) (h241 : s 241 = []) (h246 : s 246 = []) :
    ExecutesIn command
      (3500000 * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2)
      s (output p D M s t z o P N Cb O Z J) := by
  let B := baseWidth p (D + 1)
  let F := defect p D M t z o P N O
  let I := inverseValue p D M t z o F O Z Cb
  let s₁ := defectState p D M s t z o P N O Z
  let s₂ := Function.update (Function.update s₁ 240 (encode p (D + 1) I))
    241 (encode p (D + 1) Cb)
  have H₁ : Ready p D M s₁ t width frame := by
    apply ready_update p D M _ t width frame _ 241 _ (by decide) (by decide) (by decide)
    apply ready_update p D M _ t width frame _ 240 _ (by decide) (by decide) (by decide)
    exact ready_update p D M s t width frame H 222 _ (by decide) (by decide) (by decide)
  have H₂ : Ready p D M s₂ t width frame := by
    apply ready_update p D M _ t width frame _ 241 _ (by decide) (by decide) (by decide)
    exact ready_update p D M s₁ t width frame H₁ 240 _ (by decide) (by decide) (by decide)
  have h₁ : ExecutesIn prepareDefect (670000 * (D + 1)^3 * (B + 1)^2) s s₁ :=
    prepareDefect_value p D M s t z o P N O Z width frame H hleft hnegative hone
      hzero hzero' (by simp [hD]) h222 h241
  have h₂ : ExecutesIn inverse (2200000 * (D + 1)^4 * (B + 1)^2) s₁ s₂ :=
    inverse_value p D M s₁ t z o F O Z Cb width frame H₁
      (by simp [s₁, defectState]) (by simp [s₁, defectState, F])
      (by simp [s₁, defectState, hone]) (by simp [s₁, defectState, F])
      (by simp [s₁, defectState, hseed]) (by simp [s₁, defectState, hzero])
      (by simp [s₁, defectState, hD]) (by simp [s₁, defectState, h246])
  have he : Function.update (Function.update s₂ 241 (encode p (D + 1) J))
      244 (encode p (D + 1) (next p (D + 1) M t z J I)) =
      output p D M s t z o P N Cb O Z J := by
    funext i
    by_cases h244' : i = 244 <;> by_cases h241' : i = 241 <;> by_cases h240' : i = 240 <;>
      simp [s₂, s₁, defectState, output, F, I, Function.update_apply, h244', h241', h240']
  have h₃ : ExecutesIn correction (602000 * (D + 1)^3 * (B + 1)^2) s₂
      (output p D M s t z o P N Cb O Z J) := by
    have h := correction_value p D M s₂ t z I Cb J width frame H₂
      (by simp [s₂]) (by simp [s₂]) (by simp [s₂, s₁, defectState, hjet])
      (by simp [s₂, s₁, defectState, hzero]) (by simp [s₂, s₁, defectState, hD])
    rw [he] at h
    exact h
  have h := h₁.seq (h₂.seq h₃)
  apply h.mono
  dsimp only [B]
  ring_nf
  omega

end SubexponentialSAT.SubexpLocalGeometricProgram

end OAI.Algorithms
