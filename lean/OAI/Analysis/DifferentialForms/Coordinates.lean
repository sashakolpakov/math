import Mathlib
import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType

/-! # Coordinates -/

namespace OAI.Analysis.DifferentialForms.Coordinates.LocalApproximation

noncomputable section

section

/-
Modeling: use the original orthogonal basis to identify W with E². Compact
periods are encoded by complementary projectors; their ranges must be
identified, after tensoring with the fixed rank-three factor, with the
manuscript's total period subspaces. Instantiate dOld,dNew by
dᵢ(τ) = vᵢ(τ⁻¹), and determine η from PrescribedSigns's polarization convention.
Qμ and thetaTop expose the remaining geometric interfaces, with the total
μ, μ̄ prescription and the original nonzero theta top form at level N fixed.
These definitions reproduce the committed specification, with the reserved
identifier Σ renamed Place. The accompanying proof checks these definitions.
-/

open scoped Classical BigOperators _root_.Matrix
open _root_.Module

abbrev W (K : Type*) := Fin 2 → K
abbrev CompactPeriod := Matrix (Fin 2) (Fin 2) ℂ ×
  Matrix (Fin 2) (Fin 2) ℂ

-- Coordinates for the μ and μ̄ embedding spaces of V ⊗ W.
abbrev MuAmbient :=
  (Fin 3 → W ℂ) × (Fin 3 → W ℂ)

abbrev PeriodData (Place X : Type*) (μ : Place) :=
  (X → Submodule ℂ MuAmbient) ×
    ({τ : Place // τ ≠ μ} → CompactPeriod)

def hermitian
    {E : Type*} [Field E] [Algebra ℚ E]
    [NumberField E] [NumberField.IsCMField E]
    (a : Fin 2 → E) (x y : W E) : E :=
  ∑ j, a j * x j *
    NumberField.IsCMField.complexConj E (y j)

def localBasisMatrix
    {E : Type*} [Field E] [Algebra ℚ E]
    (σ : E →ₐ[ℚ] ℂ) (b : Basis (Fin 2) E (W E)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun j i => σ (b i j)

-- P selects the multiplicity lines labeled true.
-- Following PrescribedSigns, the τ-period uses the false lines, while the
-- τ̄-period uses the conjugates of the true lines.
def compactPeriod
    {E : Type*} [Field E] [Algebra ℚ E]
    (σ : E →ₐ[ℚ] ℂ) (b : Basis (Fin 2) E (W E))
    (d : Fin 2 → Bool) : CompactPeriod :=
  let C := localBasisMatrix σ b
  let P := C * Matrix.diagonal
    (fun i => if d i then (1 : ℂ) else 0) * C⁻¹
  (1 - P, fun j k => star (P j k))

def totalPeriod
    {E Place X : Type*} [Field E] [Algebra ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ) (μ : Place)
    (Qμ : X → Submodule ℂ MuAmbient)
    (b : Basis (Fin 2) E (W E))
    (d : Fin 2 → Place → Bool) : PeriodData Place X μ :=
  (Qμ, fun τ => compactPeriod (σ τ.val) b
    (fun i => d i τ.val))

section Algebra

variable {K : Type*} [Field K]

def splitMatrix (c : K →+* K) (a : Fin 2 → K) (t : K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![1 - t, -a 1 * c t; t, a 0 * c (1 - t)]

def splitNorm (c : K →+* K) (a : Fin 2 → K) (t : K) : K :=
  a 0 * (1 - t) * c (1 - t) + a 1 * t * c t

lemma splitMatrix_det (c : K →+* K) (a : Fin 2 → K) (t : K) :
    (splitMatrix c a t).det = splitNorm c a t := by
  simp [splitMatrix, splitNorm, Matrix.det_fin_two]
  ring

def basisOfMatrix (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0) :
    Basis (Fin 2) K (W K) :=
  (Pi.basisFun K (Fin 2)).map
    (M.toLinearEquiv (Pi.basisFun K (Fin 2)) (isUnit_iff_ne_zero.mpr h))

lemma basisOfMatrix_apply (M : Matrix (Fin 2) (Fin 2) K) (h : M.det ≠ 0)
    (i j : Fin 2) : basisOfMatrix M h i j = M j i := by
  fin_cases i <;> simp [basisOfMatrix, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

end Algebra

variable {E : Type*} [Field E] [Algebra ℚ E] [NumberField E]
  [NumberField.IsCMField E]

lemma hermitian_add_right (a : Fin 2 → E) (x y z : W E) :
    hermitian a x (y + z) = hermitian a x y + hermitian a x z := by
  simp [hermitian, mul_add, Finset.sum_add_distrib]

lemma hermitian_smul_right (a : Fin 2 → E) (x y : W E) (r : E) :
    hermitian a x (r • y) =
      NumberField.IsCMField.complexConj E r * hermitian a x y := by
  simp [hermitian, Fin.sum_univ_two]
  ring

lemma orthocomplement_of_basis (a : Fin 2 → E)
    (b : Basis (Fin 2) E (W E))
    (horth : hermitian a (b 0) (b 1) = 0)
    (hn : hermitian a (b 0) (b 0) ≠ 0) (y : W E) :
    y ∈ Submodule.span E {b 1} ↔ hermitian a (b 0) y = 0 := by
  constructor
  · intro hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [hermitian_smul_right, horth, mul_zero]
  · intro hy
    have hex : b.repr y 0 • b 0 + b.repr y 1 • b 1 = y := by
      simpa only [Fin.sum_univ_two] using b.sum_repr y
    have hz := hy
    rw [← hex, hermitian_add_right, hermitian_smul_right,
      hermitian_smul_right, horth, mul_zero, add_zero] at hz
    have hc : NumberField.IsCMField.complexConj E (b.repr y 0) = 0 :=
      (mul_eq_zero.mp hz).resolve_right hn
    have hzero : b.repr y 0 = 0 :=
      (NumberField.IsCMField.complexConj E).injective (by simpa using hc)
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b.repr y 1, ?_⟩
    simpa only [hzero, zero_smul, zero_add] using hex

lemma split_basis_orthogonal (a : Fin 2 → E)
    (ha : ∀ i, NumberField.IsCMField.complexConj E (a i) = a i)
    (t : E)
    (h : (splitMatrix (NumberField.IsCMField.complexConj E).toRingHom a t).det ≠ 0) :
    let b := basisOfMatrix (splitMatrix
      (NumberField.IsCMField.complexConj E).toRingHom a t) h
    hermitian a (b 0) (b 1) = 0 := by
  simp [hermitian, basisOfMatrix_apply, splitMatrix, map_mul,
    NumberField.IsCMField.complexConj_apply_apply, ha]
  ring

end

/- Local continuity of the explicit orthogonal splitting. The period coordinates
are the same complementary projectors as in the statement specification. -/

open scoped Classical BigOperators _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise
open _root_.Module

def matrixPeriod (C : Matrix (Fin 2) (Fin 2) ℂ)
    (d : Fin 2 → Bool) : CompactPeriod :=
  let P := C * Matrix.diagonal (fun i => if d i then (1 : ℂ) else 0) * C⁻¹
  (1 - P, fun j k => star (P j k))

def localSelf (a : Fin 2 → ℂ) (x : W ℂ) : ℝ :=
  (∑ j, a j * x j * star (x j)).re

def localMatrix (a : Fin 2 → ℂ) (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  splitMatrix (starRingEnd ℂ) a t

def Good (a : Fin 2 → ℂ) (η : ℝ) (d : Fin 2 → Bool)
    (P : CompactPeriod) (ε : ℝ) (t : ℂ) : Prop :=
  (localMatrix a t).det ≠ 0 ∧
  (∀ i, 0 < (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d i) : ℝ) * η *
    localSelf a (fun j => localMatrix a t j i)) ∧
  dist (matrixPeriod (localMatrix a t) d) P < ε

lemma localMatrix_continuous (a : Fin 2 → ℂ) : Continuous (localMatrix a) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [localMatrix, splitMatrix] <;> fun_prop

lemma localSelf_continuous (a : Fin 2 → ℂ) (i : Fin 2) :
    Continuous (fun t => localSelf a (fun j => localMatrix a t j i)) := by
  unfold localSelf localMatrix splitMatrix
  fun_prop

lemma matrixPeriod_continuousAt (C : Matrix (Fin 2) (Fin 2) ℂ)
    (hC : C.det ≠ 0) (d : Fin 2 → Bool) :
    ContinuousAt (fun M => matrixPeriod M d) C := by
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin 2) (Fin 2) ℂ → _) C :=
    continuousAt_matrix_inv C (by simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ hC))
  have hp : ContinuousAt
      (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
        M * Matrix.diagonal (fun i => if d i then (1 : ℂ) else 0) * M⁻¹) C :=
    (continuousAt_id.mul continuousAt_const).mul hinv
  exact (continuousAt_const.sub hp).prodMk
    (continuousAt_pi.mpr (fun j => continuousAt_pi.mpr (fun k =>
      ((continuous_apply k).continuousAt.comp
        ((continuous_apply j).continuousAt.comp hp)).star)))

lemma good_neighborhood (a : Fin 2 → ℂ) (η : ℝ) (d : Fin 2 → Bool)
    (P : CompactPeriod) (ε : ℝ) (t₀ : ℂ)
    (h : Good a η d P ε t₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, dist t t₀ < δ → Good a η d P ε t := by
  have hd : ∀ᶠ t in 𝓝 t₀, (localMatrix a t).det ≠ 0 :=
    (localMatrix_continuous a).matrix_det.continuousAt.eventually_ne h.1
  have hs : ∀ᶠ t in 𝓝 t₀, ∀ i,
      0 < (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d i) : ℝ) * η *
        localSelf a (fun j => localMatrix a t j i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact continuousAt_const.eventually_lt
      (continuousAt_const.mul (localSelf_continuous a i).continuousAt) (h.2.1 i)
  have hp : ∀ᶠ t in 𝓝 t₀,
      dist (matrixPeriod (localMatrix a t) d) P < ε :=
    (((matrixPeriod_continuousAt _ h.1 d).comp
      (localMatrix_continuous a).continuousAt).dist continuousAt_const).eventually_lt
      continuousAt_const h.2.2
  have hall : ∀ᶠ t in 𝓝 t₀, Good a η d P ε t := by
    filter_upwards [hd, hs, hp] with t hd hs hp
    exact ⟨hd, hs, hp⟩
  rcases Metric.eventually_nhds_iff.mp hall with ⟨δ, hδ, hh⟩
  exact ⟨δ, hδ, hh⟩

lemma localMatrix_zero (a : Fin 2 → ℂ) :
    localMatrix a 0 = Matrix.diagonal ![1, a 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [localMatrix, splitMatrix, Matrix.diagonal]

lemma localMatrix_one (a : Fin 2 → ℂ) :
    localMatrix a 1 = !![0, -a 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [localMatrix, splitMatrix]

lemma localMatrix_zero_det (a : Fin 2 → ℂ) : (localMatrix a 0).det = a 0 := by
  simp [localMatrix, splitMatrix_det, splitNorm]

lemma localMatrix_one_det (a : Fin 2 → ℂ) : (localMatrix a 1).det = a 1 := by
  simp [localMatrix, splitMatrix_det, splitNorm]

lemma localMatrix_zero_inv (a : Fin 2 → ℂ) (ha : a 0 ≠ 0) :
    (localMatrix a 0)⁻¹ = !![1, 0; 0, (a 0)⁻¹] := by
  apply Matrix.inv_eq_right_inv
  rw [localMatrix_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, ha]

lemma period_zero (a : Fin 2 → ℂ) (ha : a 0 ≠ 0) (d : Fin 2 → Bool) :
    matrixPeriod (localMatrix a 0) d = matrixPeriod 1 d := by
  unfold matrixPeriod
  rw [localMatrix_zero_inv a ha, localMatrix_zero]
  apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    cases hd0 : d 0 <;> cases hd1 : d 1 <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, ha, hd0, hd1]

lemma localMatrix_one_inv (a : Fin 2 → ℂ) (ha : a 1 ≠ 0) :
    (localMatrix a 1)⁻¹ = !![0, 1; -(a 1)⁻¹, 0] := by
  apply Matrix.inv_eq_right_inv
  rw [localMatrix_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha]

lemma period_one (a : Fin 2 → ℂ) (ha : a 1 ≠ 0) (d : Fin 2 → Bool) :
    matrixPeriod (localMatrix a 1) d = matrixPeriod 1 ![d 1, d 0] := by
  unfold matrixPeriod
  rw [localMatrix_one_inv a ha, localMatrix_one]
  apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    cases hd0 : d 0 <;> cases hd1 : d 1 <;>
    simp [Matrix.mul_apply, Matrix.diagonal,
      Matrix.vecHead, Matrix.vecTail, ha, hd0, hd1]

lemma localSelf_smul (a : Fin 2 → ℂ) (x : W ℂ) (r : ℂ) :
    localSelf a (r • x) = Complex.normSq r * localSelf a x := by
  simp only [localSelf, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, star_mul]
  have hr : r * star r = (Complex.normSq r : ℂ) := Complex.mul_conj r
  calc
    _ = ((r * star r) *
      (a 0 * x 0 * star (x 0) + a 1 * x 1 * star (x 1))).re := by congr 1; ring
    _ = _ := by rw [hr]; simp [Complex.mul_re]

lemma localSelf_axis (a : Fin 2 → ℂ) (i : Fin 2) :
    localSelf a (Pi.single i 1) = (a i).re := by
  fin_cases i <;> simp [localSelf, Fin.sum_univ_two]

lemma localSelf_zero (a : Fin 2 → ℂ) (i : Fin 2) :
    localSelf a (fun j => localMatrix a 0 j i) =
      if i = 0 then (a 0).re else Complex.normSq (a 0) * (a 1).re := by
  fin_cases i
  · simp [localSelf, localMatrix, splitMatrix]
  · have he : (fun j => localMatrix a 0 j 1) = a 0 • Pi.single 1 (1 : ℂ) := by
      ext j; fin_cases j <;> simp [localMatrix, splitMatrix]
    simpa using (congrArg (localSelf a) he).trans
      ((localSelf_smul a _ _).trans (by simp [localSelf_axis]))

lemma localSelf_one (a : Fin 2 → ℂ) (i : Fin 2) :
    localSelf a (fun j => localMatrix a 1 j i) =
      if i = 0 then (a 1).re else Complex.normSq (a 1) * (a 0).re := by
  fin_cases i
  · simp [localSelf, localMatrix, splitMatrix]
  · have he : (fun j => localMatrix a 1 j 1) = -a 1 • Pi.single 0 (1 : ℂ) := by
      ext j; fin_cases j <;> simp [localMatrix, splitMatrix]
    simpa using (congrArg (localSelf a) he).trans
      ((localSelf_smul a _ _).trans (by simp [localSelf_axis]))

lemma signs_reorder (dOld dNew : Fin 2 → Bool)
    (h : AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dOld 0) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dOld 1) =
      AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dNew 0) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dNew 1)) :
    (dNew 0 = dOld 0 ∧ dNew 1 = dOld 1) ∨
    (dNew 0 = dOld 1 ∧ dNew 1 = dOld 0) := by
  cases h0 : dOld 0 <;> cases h1 : dOld 1 <;>
    cases h2 : dNew 0 <;> cases h3 : dNew 1 <;> simp_all [AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue]

lemma exists_good_endpoint (a : Fin 2 → ℂ) (ha : ∀ i, a i ≠ 0)
    (η : ℝ) (dOld dNew : Fin 2 → Bool)
    (hbalance : AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dOld 0) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dOld 1) =
      AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dNew 0) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dNew 1))
    (hs : ∀ i, 0 < (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dOld i) : ℝ) * η * (a i).re)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : Bool, Good a η dNew (matrixPeriod 1 dOld) ε
      (if r then 1 else 0) := by
  rcases signs_reorder dOld dNew hbalance with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have he : dNew = dOld := by
      funext i; fin_cases i <;> assumption
    subst dNew
    refine ⟨false, ?_⟩
    change Good a η dOld (matrixPeriod 1 dOld) ε 0
    refine ⟨by simpa only [localMatrix_zero_det] using ha 0, ?_, ?_⟩
    · intro i
      rw [localSelf_zero]
      fin_cases i
      · simpa using hs 0
      · change 0 < (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dOld 1) : ℝ) * η *
          (Complex.normSq (a 0) * (a 1).re)
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_pos (Complex.normSq_pos.mpr (ha 0)) (hs 1)
    · rw [period_zero a (ha 0), dist_self]
      exact hε
  · have he : ![dNew 1, dNew 0] = dOld := by
      funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨true, ?_⟩
    change Good a η dNew (matrixPeriod 1 dOld) ε 1
    refine ⟨by simpa only [localMatrix_one_det] using ha 1, ?_, ?_⟩
    · intro i
      rw [localSelf_one]
      fin_cases i
      · change 0 < (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dNew 0) : ℝ) * η * (a 1).re
        rw [h0]
        exact hs 1
      · change 0 < (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (dNew 1) : ℝ) * η *
          (Complex.normSq (a 1) * (a 0).re)
        rw [h1]
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_pos (Complex.normSq_pos.mpr (ha 1)) (hs 0)
    · rw [period_one a (ha 1), he, dist_self]
      exact hε

variable {E : Type*} [Field E] [Algebra ℚ E] [NumberField E]
  [NumberField.IsCMField E]

lemma embedding_splitMatrix (σ : E →ₐ[ℚ] ℂ) (a : Fin 2 → E) (t : E) :
    (splitMatrix (NumberField.IsCMField.complexConj E).toRingHom a t).map σ =
      localMatrix (fun i => σ (a i)) (σ t) := by
  have hc (x : E) : σ (NumberField.IsCMField.complexConj E x) = star (σ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj E σ.toRingHom x
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitMatrix, localMatrix, hc]

lemma embedding_basis (σ : E →ₐ[ℚ] ℂ) (a : Fin 2 → E) (t : E)
    (h : (splitMatrix (NumberField.IsCMField.complexConj E).toRingHom a t).det ≠ 0) :
    localBasisMatrix σ
      (basisOfMatrix (splitMatrix (NumberField.IsCMField.complexConj E).toRingHom a t) h) =
        localMatrix (fun i => σ (a i)) (σ t) := by
  rw [← embedding_splitMatrix σ a t]
  ext i j
  simp only [localBasisMatrix, basisOfMatrix_apply, Matrix.map_apply]

lemma embedding_hermitian_self (σ : E →ₐ[ℚ] ℂ) (a : Fin 2 → E) (x : W E) :
    (σ (hermitian a x x)).re =
      localSelf (fun i => σ (a i)) (fun i => σ (x i)) := by
  have hc (y : E) : σ (NumberField.IsCMField.complexConj E y) = star (σ y) :=
    NumberField.IsCMField.complexEmbedding_complexConj E σ.toRingHom y
  simp [hermitian, localSelf, hc]

omit [NumberField E] [NumberField.IsCMField E] in
lemma original_basis_matrix (σ : E →ₐ[ℚ] ℂ) :
    localBasisMatrix σ (Pi.basisFun E (Fin 2)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [localBasisMatrix]

end

end OAI.Analysis.DifferentialForms.Coordinates.LocalApproximation
