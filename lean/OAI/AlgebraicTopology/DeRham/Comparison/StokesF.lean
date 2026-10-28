import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-! # Stokes F -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.StokesF

noncomputable section

/-!
Smooth cubical integration and its integer-linear boundary.
Coordinate faces use insertion of a fixed coordinate. The boundary is the
linear extension of signed upper and lower faces, and integration evaluates
pullbacks on the standard frame. Stokes' identity follows from the divergence
theorem; the boundary squares to zero by paired codimension-two faces.
-/

open scoped ContDiff BigOperators _root_.Topology

namespace Stokes

/-- The real coordinate space in dimension `d`. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- A smooth parameterized cube, with a global smoothness certificate. -/
@[ext]
structure Cube (d m : ℕ) where
  toFun : Point d → Point m
  smooth : ContDiff ℝ ∞ toFun

instance {d m : ℕ} : CoeFun (Cube d m) (fun _ => Point d → Point m) :=
  ⟨Cube.toFun⟩

/-- A differential `k`-form on the coordinate space of dimension `m`. -/
abbrev Form (m k : ℕ) := Point m → Point m [⋀^Fin k]→L[ℝ] ℝ

/-- Insert a fixed coordinate to parameterize a face. -/
def coordinateFace {n : ℕ} (i : Fin (n + 1)) (t : ℝ) :
    Point n → Point (n + 1) :=
  Fin.insertNth (α := fun _ => ℝ) i t

/-- Coordinate-face parameterizations are smooth. -/
theorem smooth_coordinateFace {n : ℕ} (i : Fin (n + 1)) (t : ℝ) :
    ContDiff ℝ ∞ (coordinateFace i t) := by
  apply contDiff_pi.mpr
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨l, rfl⟩
  · simpa only [coordinateFace, Fin.insertNth_apply_same] using
      (contDiff_const : ContDiff ℝ ∞ fun _ : Point n => t)
  · simpa only [coordinateFace, Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℝ ℝ l : ContDiff ℝ ∞ fun x : Point n => x l)

/-- The coordinate-face map is tuple insertion. -/
@[simp] theorem coordinateFace_apply {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (x : Point n) : coordinateFace i t x = Fin.insertNth i t x :=
  rfl

/-- Restrict a smooth cube to one coordinate face. -/
def face {n m : ℕ} (c : Cube (n + 1) m) (i : Fin (n + 1)) (t : ℝ) : Cube n m where
  toFun := c ∘ coordinateFace i t
  smooth := c.smooth.comp (smooth_coordinateFace i t)

def unitCube (n : ℕ) : Set (Point n) :=
  Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1)

def identityCube (n : ℕ) : Cube n n where
  toFun := id
  smooth := contDiff_id

def orientation {n : ℕ} (i : Fin (n + 1)) (upper : Bool) : ℤ :=
  if upper then (-1 : ℤ) ^ i.val else (-1 : ℤ) ^ (i.val + 1)

/-- Finite integer combinations of smooth cubes. -/
abbrev Chain (d m : ℕ) := Cube d m →₀ ℤ

/-- The signed sum of upper and lower faces of a cube. -/
def boundaryGenerator {n m : ℕ} (σ : Cube (n + 1) m) : Chain n m :=
  ∑ i : Fin (n + 1),
    (Finsupp.single (face σ i 1) ((-1 : ℤ) ^ i.val) +
      Finsupp.single (face σ i 0) ((-1 : ℤ) ^ (i.val + 1)))

/-- Extend the signed face sum linearly to chains. -/
def boundaryLinear (n m : ℕ) : Chain (n + 1) m →ₗ[ℤ] Chain n m :=
  Finsupp.linearCombination ℤ boundaryGenerator

def boundary {n m : ℕ} (c : Chain (n + 1) m) : Chain n m :=
  boundaryLinear n m c

/-- Pull a form back along a smooth cube. -/
def pullback {d m k : ℕ} (σ : Cube d m) (η : Form m k) : Form d k :=
  fun x => (η (σ.toFun x)).compContinuousLinearMap (fderiv ℝ σ.toFun x)

/-- Integrate a top-degree pullback on the unit cube. -/
def integral {d m : ℕ} (σ : Cube d m) (η : Form m d) : ℝ :=
  ∫ x in unitCube d, pullback σ η x (fun j => Pi.single j 1)

/-- Extend cube integration to integer chains. -/
def chainIntegral {n m : ℕ} (c : Chain n m) (η : Form m n) : ℝ :=
  c.sum (fun σ k => (k : ℝ) * integral σ η)

section ChainAlgebra

variable {n d m : ℕ}

/-- The empty chain has empty boundary. -/
@[simp] theorem boundary_empty : boundary (0 : Chain (n + 1) m) = 0 := by
  exact (boundaryLinear n m).map_zero

/-- Boundary commutes with chain addition. -/
theorem boundary_sum (a b : Chain (n + 1) m) :
    boundary (a + b) = boundary a + boundary b := by
  exact (boundaryLinear n m).map_add a b

/-- A generator coefficient scales its signed face sum. -/
theorem boundary_generator (σ : Cube (n + 1) m) (k : ℤ) :
    boundary (Finsupp.single σ k) = k • boundaryGenerator σ := by
  exact Finsupp.linearCombination_single ℤ k σ

theorem boundary_scalar (k : ℤ) (c : Chain (n + 1) m) :
    boundary (k • c) = k • boundary c := by
  exact (boundaryLinear n m).map_smul k c

theorem boundary_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Chain (n + 1) m) :
    boundary (∑ i ∈ s, f i) = ∑ i ∈ s, boundary (f i) := by
  exact map_sum (boundaryLinear n m) _ _

/-- Integration of a chain, bundled as an integer-linear map. -/
def chainIntegralLinear (η : Form m d) : Chain d m →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ (fun σ => integral σ η)

theorem chainIntegral_eq_linear (c : Chain d m) (η : Form m d) :
    chainIntegral c η = chainIntegralLinear η c := by
  simp only [chainIntegral, chainIntegralLinear, Finsupp.linearCombination_apply,
    zsmul_eq_mul]

@[simp] theorem chainIntegral_empty (η : Form m d) :
    chainIntegral (0 : Chain d m) η = 0 := by
  rw [chainIntegral_eq_linear]
  exact (chainIntegralLinear η).map_zero

theorem chainIntegral_sum (a b : Chain d m) (η : Form m d) :
    chainIntegral (a + b) η = chainIntegral a η + chainIntegral b η := by
  simp only [chainIntegral_eq_linear]
  exact (chainIntegralLinear η).map_add a b

theorem chainIntegral_generator (σ : Cube d m) (k : ℤ) (η : Form m d) :
    chainIntegral (Finsupp.single σ k) η = (k : ℝ) * integral σ η := by
  rw [chainIntegral_eq_linear]
  simp only [chainIntegralLinear, Finsupp.linearCombination_single, zsmul_eq_mul]

theorem chainIntegral_smul (k : ℤ) (c : Chain d m) (η : Form m d) :
    chainIntegral (k • c) η = (k : ℝ) * chainIntegral c η := by
  simp only [chainIntegral_eq_linear]
  simpa only [zsmul_eq_mul] using (chainIntegralLinear η).map_smul k c

theorem chainIntegral_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Chain d m) (η : Form m d) :
    chainIntegral (∑ i ∈ s, f i) η = ∑ i ∈ s, chainIntegral (f i) η := by
  simp only [chainIntegral_eq_linear]
  exact map_sum (chainIntegralLinear η) _ _

theorem chainIntegral_boundary_generator (σ : Cube (n + 1) m) (η : Form m n) :
    chainIntegral (boundaryGenerator σ) η =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val *
        (integral (face σ i 1) η - integral (face σ i 0) η) := by
  classical
  unfold boundaryGenerator
  rw [chainIntegral_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [chainIntegral_sum, chainIntegral_generator, chainIntegral_generator]
  push_cast
  rw [pow_succ]
  ring

theorem chainIntegral_boundary_expand (c : Chain (n + 1) m) (η : Form m n) :
    chainIntegral (boundary c) η =
      c.sum (fun σ k => (k : ℝ) * chainIntegral (boundaryGenerator σ) η) := by
  simp only [chainIntegral_eq_linear, boundary, boundaryLinear]
  rw [Finsupp.apply_linearCombination]
  simp only [Finsupp.linearCombination_apply, Function.comp_apply, zsmul_eq_mul]

end ChainAlgebra

private theorem insertion_exchange {α : Type*} {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (a b : α) (x : Fin n → α) :
    Fin.insertNth (α := fun _ => α) i a (Fin.insertNth (α := fun _ => α) j b x) =
      Fin.insertNth (α := fun _ => α) (i.succAbove j) b (Fin.insertNth (α := fun _ => α) (j.predAbove i) a x) := by
  funext k
  obtain h | ⟨l, h⟩ := Fin.eq_self_or_eq_succAbove i k
  · subst k
    calc
      Fin.insertNth (α := fun _ => α) i a (Fin.insertNth (α := fun _ => α) j b x) i = a := by simp
      _ = Fin.insertNth (α := fun _ => α) (i.succAbove j) b (Fin.insertNth (α := fun _ => α) (j.predAbove i) a x)
          ((i.succAbove j).succAbove (j.predAbove i)) := by simp
      _ = _ := congrArg _ (Fin.succAbove_succAbove_predAbove i j)
  · subst k
    obtain h | ⟨k, h⟩ := Fin.eq_self_or_eq_succAbove j l
    · subst l
      simp
    · subst l
      calc
        Fin.insertNth (α := fun _ => α) i a (Fin.insertNth (α := fun _ => α) j b x) (i.succAbove (j.succAbove k)) = x k := by simp
        _ = Fin.insertNth (α := fun _ => α) (i.succAbove j) b (Fin.insertNth (α := fun _ => α) (j.predAbove i) a x)
            ((i.succAbove j).succAbove ((j.predAbove i).succAbove k)) := by simp
        _ = _ := congrArg _ (Fin.succAbove_succAbove_succAbove_predAbove i j k)

private theorem index_sign_exchange {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (-1 : ℤ) ^ (i.succAbove j).val * (-1 : ℤ) ^ (j.predAbove i).val =
      -((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ j.val) := by
  cases Fin.lt_or_le j.castSucc i with
  | inl h =>
    rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_castSucc, Fin.val_pred]
    have hi : 0 < i.val := by exact lt_of_le_of_lt (Nat.zero_le j.val) h
    have he : i.val = (i.val - 1) + 1 := by omega
    conv_rhs => rw [he, pow_succ]
    ring
  | inr h =>
    rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.predAbove_of_le_castSucc _ _ h]
    simp only [Fin.val_succ, Fin.coe_castPred, pow_succ]
    ring

private theorem alternating_double_sum {n : ℕ} {M : Type*} [AddCommGroup M]
    (q : Fin (n + 2) → Fin (n + 1) → M)
    (hq : ∀ i j, q (i.succAbove j) (j.predAbove i) = q i j) :
    ∑ i, ∑ j, ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ j.val) • q i j = 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun p : Fin (n + 2) × Fin (n + 1) =>
    ((-1 : ℤ) ^ p.1.val * (-1 : ℤ) ^ p.2.val) • q p.1 p.2)]
  apply Finset.sum_ninvolution (fun p : Fin (n + 2) × Fin (n + 1) =>
    (p.1.succAbove p.2, p.2.predAbove p.1))
  · rintro ⟨i, j⟩
    dsimp only
    rw [hq, index_sign_exchange, neg_smul, add_neg_cancel]
  · rintro ⟨i, j⟩ _ h
    exact Fin.succAbove_ne i j (congrArg Prod.fst h)
  · intro p
    exact Finset.mem_univ _
  · rintro ⟨i, j⟩
    exact Prod.ext (Fin.succAbove_succAbove_predAbove i j)
      (Fin.predAbove_predAbove_succAbove i j)

private theorem face_exchange {n m : ℕ} (σ : Cube (n + 2) m)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (a b : ℝ) :
    face (face σ i a) j b = face (face σ (i.succAbove j) b) (j.predAbove i) a := by
  apply Cube.ext
  funext x
  exact congrArg σ.toFun (insertion_exchange i j a b x)

private theorem generator_normalized {n m : ℕ} (σ : Cube (n + 1) m) :
    boundaryGenerator σ = ∑ i : Fin (n + 1),
      ((-1 : ℤ) ^ i.val) •
        (Finsupp.single (face σ i 1) 1 - Finsupp.single (face σ i 0) 1) := by
  classical
  unfold boundaryGenerator
  apply Finset.sum_congr rfl
  intro i _
  simp [Finsupp.smul_single, pow_succ, sub_eq_add_neg]

private def rectangle {n m : ℕ} (σ : Cube (n + 2) m)
    (i : Fin (n + 2)) (j : Fin (n + 1)) : Chain n m :=
  Finsupp.single (face (face σ i 1) j 1) 1 -
    Finsupp.single (face (face σ i 1) j 0) 1 -
    Finsupp.single (face (face σ i 0) j 1) 1 +
    Finsupp.single (face (face σ i 0) j 0) 1

private theorem rectangle_exchange {n m : ℕ} (σ : Cube (n + 2) m)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    rectangle σ (i.succAbove j) (j.predAbove i) = rectangle σ i j := by
  unfold rectangle
  rw [← face_exchange σ i j 1 1, ← face_exchange σ i j 0 1,
    ← face_exchange σ i j 1 0, ← face_exchange σ i j 0 0]
  abel

private theorem generator_second_boundary {n m : ℕ} (σ : Cube (n + 2) m) :
    boundaryLinear n m (boundaryGenerator σ) =
      ∑ i, ∑ j, ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ j.val) • rectangle σ i j := by
  classical
  have hs : ∀ τ : Cube (n + 1) m,
      boundaryLinear n m (Finsupp.single τ 1) = boundaryGenerator τ := by
    intro τ
    simp [boundaryLinear]
  rw [generator_normalized]
  simp only [map_sum, map_smul, map_sub, hs]
  simp_rw [generator_normalized]
  simp only [← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold rectangle
  simp only [smul_sub, smul_add, smul_smul]
  abel

theorem boundary_linear_squared (n m : ℕ) :
    (boundaryLinear n m).comp (boundaryLinear (n + 1) m) = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro σ k
  change boundaryLinear n m (boundaryLinear (n + 1) m (Finsupp.single σ k)) = 0
  have hs : boundaryLinear (n + 1) m (Finsupp.single σ k) = k • boundaryGenerator σ := by
    simp [boundaryLinear]
  rw [hs, map_smul, generator_second_boundary,
    alternating_double_sum (rectangle σ) (rectangle_exchange σ), smul_zero]

/-- Every chain boundary is a cycle. -/
theorem boundary_squared {n m : ℕ} (c : Chain (n + 2) m) :
    boundary (boundary c) = 0 := by
  exact LinearMap.congr_fun (boundary_linear_squared n m) c

def coordinateFaceLinear {n : ℕ} (i : Fin (n + 1)) :
    Point n →L[ℝ] Point (n + 1) :=
  ContinuousLinearMap.pi (i.insertNth 0 (fun j => ContinuousLinearMap.proj j))

@[simp] theorem coordinateFaceLinear_apply {n : ℕ} (i : Fin (n + 1))
    (v : Point n) : coordinateFaceLinear i v = i.insertNth 0 v := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩ <;>
    simp [coordinateFaceLinear]

theorem hasFDerivAt_coordinateFace {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (x : Point n) :
    HasFDerivAt (coordinateFace i t) (coordinateFaceLinear i) x := by
  unfold coordinateFace coordinateFaceLinear
  apply hasFDerivAt_pi.mpr
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simpa only [Fin.insertNth_apply_same] using
      (hasFDerivAt_const (𝕜 := ℝ) t x)
  · simpa only [Fin.insertNth_apply_succAbove] using
      (hasFDerivAt_apply (𝕜 := ℝ) j x)

theorem fderiv_coordinateFace {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (x : Point n) :
    fderiv ℝ (coordinateFace i t) x = coordinateFaceLinear i :=
  (hasFDerivAt_coordinateFace i t x).fderiv

@[simp] theorem coordinateFaceLinear_standard {n : ℕ} (i : Fin (n + 1))
    (j : Fin n) :
    coordinateFaceLinear i (Pi.single j 1) = Pi.single (i.succAbove j) 1 := by
  rw [coordinateFaceLinear_apply]
  ext l
  rcases Fin.eq_self_or_eq_succAbove i l with rfl | ⟨l, rfl⟩
  · simp
  · simp [Pi.single_apply]

theorem fderiv_face {n m : ℕ} (σ : Cube (n + 1) m) (i : Fin (n + 1))
    (t : ℝ) (x : Point n) :
    fderiv ℝ (face σ i t).toFun x =
      (fderiv ℝ σ.toFun (coordinateFace i t x)).comp (coordinateFaceLinear i) := by
  exact ((σ.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    (hasFDerivAt_coordinateFace i t x)).fderiv

theorem pullback_face {n m k : ℕ} (σ : Cube (n + 1) m)
    (η : Form m k) (i : Fin (n + 1)) (t : ℝ) (x : Point n)
    (v : Fin k → Point n) :
    pullback (face σ i t) η x v =
      pullback σ η (coordinateFace i t x) (fun j => coordinateFaceLinear i (v j)) := by
  simp only [pullback, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [fderiv_face]
  rfl

theorem pullback_face_standard {n m : ℕ} (σ : Cube (n + 1) m)
    (η : Form m n) (i : Fin (n + 1)) (t : ℝ) (x : Point n) :
    pullback (face σ i t) η x (fun j => Pi.single j 1) =
      pullback σ η (coordinateFace i t x) (i.removeNth (fun j => (Pi.single j 1 : Point (n + 1)))) := by
  rw [pullback_face]
  congr 1
  funext j
  exact coordinateFaceLinear_standard i j

open _root_.MeasureTheory Set _root_.ContinuousAlternatingMap

variable {n m d k : ℕ}

theorem differentiable_exterior_form (η : Form m n)
    (hη : ContDiff ℝ ∞ η) : Differentiable ℝ (extDeriv η) := by
  change Differentiable ℝ (fun x =>
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Point m) ℝ (fderiv ℝ η x))
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Point m) ℝ).differentiable.comp
    (contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp hη).2).1

theorem differentiable_pullback (σ : Cube d m) (η : Form m k)
    (hη : Differentiable ℝ η) : Differentiable ℝ (pullback σ η) := by
  intro x
  exact ((hη.comp (contDiff_infty_iff_fderiv.mp σ.smooth).1) x).continuousAlternatingMapCompContinuousLinearMap
      ((contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp σ.smooth).2).1 x)

theorem pullback_exterior_standard (σ : Cube (n + 1) m) (η : Form m n)
    (hη : ContDiff ℝ ∞ η) (x : Point (n + 1)) :
    pullback σ (extDeriv η) x (fun j => Pi.single j 1) =
      ∑ i : Fin (n + 1),
        fderiv ℝ (fun y => (-1 : ℝ) ^ i.val *
          pullback σ η y (i.removeNth (fun j => (Pi.single j 1 : Point (n + 1)))))
          x (Pi.single i 1) := by
  have hpb : Differentiable ℝ (pullback σ η) :=
    differentiable_pullback σ η (contDiff_infty_iff_fderiv.mp hη).1
  have hp : extDeriv (pullback σ η) x = pullback σ (extDeriv η) x := by
    apply extDeriv_pullback (r := (2 : ℕ∞ω))
      ((contDiff_infty_iff_fderiv.mp hη).1 (σ.toFun x))
      (σ.smooth.of_le ?_).contDiffAt ?_
    · exact WithTop.coe_le_coe.mpr le_top
    · simp
  rw [← hp, extDeriv_apply (hpb x)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_const_mul ((hpb.continuousAlternatingMap_apply_const _) x)]
  simp

/-- Stokes' identity for a smooth cube and a smooth form. -/
theorem integral_derivative_cube (σ : Cube (n + 1) m) (η : Form m n)
    (hη : ContDiff ℝ ∞ η) :
    integral σ (extDeriv η) =
      ∑ i : Fin (n + 1), (-1 : ℝ)^i.val *
        (integral (face σ i 1) η - integral (face σ i 0) η) := by
  let f : Fin (n + 1) → Point (n + 1) → ℝ := fun i x =>
    (-1 : ℝ)^i.val *
      pullback σ η x (i.removeNth (fun j => (Pi.single j 1 : Point (n + 1))))
  have hpb := differentiable_pullback σ η (contDiff_infty_iff_fderiv.mp hη).1
  have hd : ∀ i, Differentiable ℝ (f i) := fun i =>
    ((hpb.continuousAlternatingMap_apply_const _).const_mul _)
  have he : ∀ x, pullback σ (extDeriv η) x (fun j => Pi.single j 1) =
      ∑ i : Fin (n + 1), fderiv ℝ (f i) x (Pi.single i 1) :=
    pullback_exterior_standard σ η hη
  have hint : IntegrableOn
      (fun x => ∑ i : Fin (n + 1), fderiv ℝ (f i) x (Pi.single i 1)) (unitCube (n + 1)) := by
    have hc := (differentiable_pullback σ (extDeriv η)
      (differentiable_exterior_form η hη)).continuousAlternatingMap_apply_const
        (fun j => (Pi.single j 1 : Point (n + 1)))
    simpa only [← he, unitCube] using hc.continuous.integrableOn_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable'
    (fun _ : Fin (n + 1) => (0 : ℝ)) (fun _ => (1 : ℝ))
    (by intro i; norm_num) f (fun i x => fderiv ℝ (f i) x)
    ∅ Set.countable_empty
    (fun i => (hd i).continuous.continuousOn)
    (fun x hx i => (hd i x).hasFDerivAt) hint
  unfold integral
  simp only [he, unitCube]
  rw [hdiv]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [f]
  rw [integral_const_mul, integral_const_mul]
  rw [mul_sub]
  congr 1 <;> congr 1 <;> apply setIntegral_congr_fun measurableSet_Icc <;>
    intro x hx <;> exact (pullback_face_standard σ η i _ x).symm

/-- Stokes' identity extended to integer chains. -/
theorem integral_derivative_chain (c : Chain (n + 1) m) (η : Form m n)
    (hη : ContDiff ℝ ∞ η) :
    chainIntegral (boundary c) η = chainIntegral c (extDeriv η) := by
  rw [chainIntegral_boundary_expand]
  conv_rhs => unfold chainIntegral
  apply Finsupp.sum_congr
  intro σ hσ
  rw [chainIntegral_boundary_generator, ← integral_derivative_cube σ η hη]

end Stokes

-- Definition aliases keep existing theorem statements stable.
namespace SingularCubeStokes

abbrev SmoothSingularCube (n m : ℕ) := Stokes.Cube n m
abbrev SingularChain (n m : ℕ) := Stokes.Chain n m
abbrev faceInclusion {n : ℕ} (i : Fin (n + 1)) (t : ℝ) := Stokes.coordinateFace i t
abbrev singularFace {n m : ℕ} (σ : SmoothSingularCube (n + 1) m)
    (i : Fin (n + 1)) (t : ℝ) := Stokes.face σ i t
abbrev unitCube (n : ℕ) := Stokes.unitCube n
abbrev idCube (n : ℕ) := Stokes.identityCube n
abbrev boundarySign {n : ℕ} (i : Fin (n + 1)) (hi : Bool) := Stokes.orientation i hi
abbrev singularBoundarySingle {n m : ℕ} (σ : SmoothSingularCube (n + 1) m) :=
  Stokes.boundaryGenerator σ
abbrev singularBoundary {n m : ℕ} (c : SingularChain (n + 1) m) :=
  Stokes.boundary c
abbrev singularBoundaryHom (n m : ℕ) := (Stokes.boundaryLinear n m).toAddMonoidHom
abbrev pullbackForm {d m k : ℕ} (σ : SmoothSingularCube d m) (η : Stokes.Form m k) :=
  Stokes.pullback σ η
abbrev integrateForm {d m : ℕ} (σ : SmoothSingularCube d m) (η : Stokes.Form m d) :=
  Stokes.integral σ η
abbrev integrateChain {n m : ℕ} (c : SingularChain n m) (η : Stokes.Form m n) :=
  Stokes.chainIntegral c η

end SingularCubeStokes

end

end OAI.AlgebraicTopology.DeRham.Comparison.StokesF
