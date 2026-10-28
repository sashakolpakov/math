import OAI.AlgebraicTopology.FundamentalClass.DuffyDerivative
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Integration Duffy Orientation -/

namespace OAI.AlgebraicTopology.FundamentalClass.IntegrationDuffyOrientation.Construction.Duffy

noncomputable section

section

/-! Integration: the omitted-barycentric-coordinate change contributes precisely
the sign used by the existing signed Duffy simplex integral. -/

open Set _root_.MeasureTheory
open scoped ContDiff

abbrev realSnoc {d : ℕ} (v : Fin d → ℝ) (a : ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc v a

def tailConstant (d : ℕ) : Fin d → ℝ :=
  Fin.tail (Pi.single (Fin.last d) (1 : ℝ) : Fin (d + 1) → ℝ)

def tailLinear (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun v := Fin.tail (realSnoc v (-∑ i, v i))
  map_add' v w := by
    have h : realSnoc (v + w) (-∑ i, (v + w) i) =
        realSnoc v (-∑ i, v i) + realSnoc w (-∑ i, w i) := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [Finset.sum_add_distrib, add_comm]
    exact congrArg Fin.tail h
  map_smul' c v := by
    have h : realSnoc (c • v) (-∑ i, (c • v) i) = c • realSnoc v (-∑ i, v i) := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;>
        simp [Finset.mul_sum, mul_neg, smul_eq_mul]
    exact congrArg Fin.tail h

theorem tailLinear_castSucc (d : ℕ) (v : Fin (d + 1) → ℝ) (i : Fin d) :
    tailLinear (d + 1) v i.castSucc = v i.succ := by
  change realSnoc v (-∑ k, v k) i.succ.castSucc = v i.succ
  simp only [realSnoc, Fin.snoc_castSucc]

theorem tailLinear_last (d : ℕ) (v : Fin (d + 1) → ℝ) :
    tailLinear (d + 1) v (Fin.last d) = -∑ k, v k := by
  change realSnoc v (-∑ k, v k) (Fin.last (d + 1)) = _
  simp only [realSnoc, Fin.snoc_last]

def tailMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d)) (tailLinear d)

theorem tailMatrix_apply (d : ℕ) (i j : Fin d) :
    tailMatrix d i j = tailLinear d (Pi.single j 1) i := by simp [tailMatrix]

theorem tailMatrix_castSucc (d : ℕ) (i : Fin d) (j : Fin (d + 1)) :
    tailMatrix (d + 1) i.castSucc j = if j = i.succ then 1 else 0 := by
  rw [tailMatrix_apply, tailLinear_castSucc]
  classical
  simp only [Pi.single_apply]
  split_ifs <;> simp_all

theorem tailMatrix_last (d : ℕ) (j : Fin (d + 1)) :
    tailMatrix (d + 1) (Fin.last d) j = -1 := by
  rw [tailMatrix_apply, tailLinear_last]
  simp

theorem tailLinear_det (d : ℕ) : (tailLinear d).det = (-1 : ℝ) ^ d := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin d))]
  change (tailMatrix d).det = _
  cases d with
  | zero => simp
  | succ d =>
    rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (Fin.last d)]
    · have hm : (tailMatrix (d + 1)).submatrix (Fin.last d).succAbove Fin.succ = 1 := by
        ext i j
        simp [Matrix.submatrix_apply, tailMatrix_castSucc, Matrix.one_apply, eq_comm]
      rw [tailMatrix_last, hm, Matrix.det_one, mul_one]
      simp [pow_succ]
    · intro i _ hi
      obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      rw [tailMatrix_castSucc]
      simp [Ne.symm (Fin.succ_ne_zero j)]
    · simp

def tailAffine (d : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  tailLinear d x + tailConstant d

theorem tailAffine_eq (d : ℕ) (x : Fin d → ℝ) :
    tailAffine d x = Fin.tail (realSnoc x (1 - ∑ i, x i)) := by
  have h : realSnoc x (-∑ i, x i) + (Pi.single (Fin.last d) (1 : ℝ) : Fin (d + 1) → ℝ) =
      realSnoc x (1 - ∑ i, x i) := by
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [sub_eq_add_neg, add_comm]
    · simp
  exact congrArg Fin.tail h

theorem tailAffine_hasFDerivAt (d : ℕ) (x : Fin d → ℝ) :
    HasFDerivAt (tailAffine d) (tailLinear d).toContinuousLinearMap x :=
  (tailLinear d).toContinuousLinearMap.hasFDerivAt.add_const _

theorem tailAffine_injective (d : ℕ) : Function.Injective (tailAffine d) := by
  intro x y h
  have hlin : tailLinear d x = tailLinear d y := add_right_cancel (show tailLinear d x + tailConstant d = tailLinear d y + tailConstant d from h)
  have hn : (tailLinear d).det ≠ 0 := by
    rw [tailLinear_det]
    exact pow_ne_zero _ (by norm_num)
  have hk : (tailLinear d).ker = ⊥ :=
    not_ne_iff.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
  exact (LinearMap.ker_eq_bot.mp hk) hlin

def tail (d : ℕ) (t : Fin d → ℝ) : Fin d → ℝ :=
  Fin.tail (DeRham.Comparison.DuffyCoordinates.Duffy.coordinates d t)

theorem coordinates_eq_snoc (d : ℕ) (t : Fin d → ℝ) :
    DeRham.Comparison.DuffyCoordinates.Duffy.coordinates d t = realSnoc (DuffyDomain.IntegrationConstruction.Duffy.front d t) (1 - ∑ i, DuffyDomain.IntegrationConstruction.Duffy.front d t i) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [realSnoc, Fin.snoc_last]
    have h := DeRham.Comparison.DuffyCoordinates.Duffy.sum_coordinates d t
    rw [Fin.sum_univ_castSucc] at h
    change (∑ i, DuffyDomain.IntegrationConstruction.Duffy.front d t i) + DeRham.Comparison.DuffyCoordinates.Duffy.coordinates d t (Fin.last d) = 1 at h
    linarith
  · simp only [realSnoc, Fin.snoc_castSucc]
    rfl

theorem tail_eq_comp (d : ℕ) : Duffy.tail d = tailAffine d ∘ DuffyDomain.IntegrationConstruction.Duffy.front d := by
  funext t
  rw [Function.comp_apply, tailAffine_eq, Duffy.tail, coordinates_eq_snoc]

theorem tail_hasFDerivAt (d : ℕ) (t : Fin d → ℝ) :
    HasFDerivAt (Duffy.tail d)
      ((tailLinear d).toContinuousLinearMap.comp (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t)) t := by
  rw [tail_eq_comp]
  exact (tailAffine_hasFDerivAt d _).comp t
    ((DuffyDomain.IntegrationConstruction.Duffy.front_contDiff d).differentiable (by simp)).differentiableAt.hasFDerivAt

theorem fderiv_tail_det (d : ℕ) (t : Fin d → ℝ) :
    (fderiv ℝ (Duffy.tail d) t).toLinearMap.det =
      (-1 : ℝ) ^ d * (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t).toLinearMap.det := by
  rw [(tail_hasFDerivAt d t).fderiv]
  change ((tailLinear d).comp (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t).toLinearMap).det = _
  rw [LinearMap.det_comp, tailLinear_det]

end

section

open Set

theorem coordinates_pos (d : ℕ) (t : Fin d → ℝ) (ht : t ∈ DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d)
    (j : Fin (d + 1)) : 0 < DeRham.Comparison.DuffyCoordinates.Duffy.coordinates d t j := by
  rw [coordinates_eq_snoc]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [realSnoc, Fin.snoc_last] using
      sub_pos.mpr (DuffyDomain.IntegrationConstruction.Duffy.front_mem_simplexInterior d t ht).2
  · simpa only [realSnoc, Fin.snoc_castSucc] using
      (DuffyDomain.IntegrationConstruction.Duffy.front_mem_simplexInterior d t ht).1 i

theorem coordinates_surjective_on_interior (d : ℕ) (z : Fin (d + 1) → ℝ)
    (hz : ∀ j, 0 < z j) (hs : ∑ j, z j = 1) :
    ∃ t ∈ DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d, DeRham.Comparison.DuffyCoordinates.Duffy.coordinates d t = z := by
  let x : Fin d → ℝ := fun i => z i.castSucc
  have hs' : (∑ i, x i) + z (Fin.last d) = 1 := by
    simpa only [x, Fin.sum_univ_castSucc] using hs
  have hx : x ∈ DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d :=
    ⟨fun i => hz i.castSucc, by linarith [hz (Fin.last d)]⟩
  refine ⟨DuffyDomain.IntegrationConstruction.Duffy.inverse d x, DuffyDomain.IntegrationConstruction.Duffy.inverse_mem_cubeInterior d x hx, ?_⟩
  rw [coordinates_eq_snoc, DuffyDomain.IntegrationConstruction.Duffy.front_inverse d x hx]
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [realSnoc, Fin.snoc_last]
    linarith
  · simp only [realSnoc, Fin.snoc_castSucc]
    rfl

theorem tail_image (d : ℕ) : Duffy.tail d '' DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d = DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    constructor
    · intro j
      exact coordinates_pos d t ht j.succ
    · have hs := DeRham.Comparison.DuffyCoordinates.Duffy.sum_coordinates d t
      rw [Fin.sum_univ_succ] at hs
      have hp := coordinates_pos d t ht 0
      change ∑ j : Fin d, DeRham.Comparison.DuffyCoordinates.Duffy.coordinates d t j.succ < 1
      linarith
  · intro x hx
    let z : Fin (d + 1) → ℝ := Fin.cons (1 - ∑ i, x i) x
    have hz : ∀ j, 0 < z j := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact sub_pos.mpr hx.2
      · exact hx.1 i
    have hs : ∑ j, z j = 1 := by
      rw [Fin.sum_univ_succ]
      simp only [z, Fin.cons_zero, Fin.cons_succ]
      ring
    obtain ⟨t, ht, heq⟩ := coordinates_surjective_on_interior d z hz hs
    refine ⟨t, ht, ?_⟩
    rw [Duffy.tail, heq]
    exact Fin.tail_cons _ _

end

/-! The signed Duffy integral is the ordinary Lebesgue integral on the
interior of the standard affine simplex. -/

open Set _root_.MeasureTheory

set_option backward.isDefEq.respectTransparency false

theorem cubeInterior_isOpen (d : ℕ) : IsOpen (DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d) := by
  change IsOpen {t : Fin d → ℝ | ∀ i, 0 < t i ∧ t i < 1}
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

theorem cubeInterior_ae_eq_Icc (d : ℕ) :
    DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d =ᵐ[volume] Icc (0 : Fin d → ℝ) 1 := by
  have h := Measure.univ_pi_Ioo_ae_eq_Icc
    (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := (0 : Fin d → ℝ)) (g := 1)
  have heq : (univ.pi fun _ : Fin d => Ioo (0 : ℝ) 1) = DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d := by
    ext t
    simp [DuffyDomain.IntegrationConstruction.Duffy.cubeInterior]
  simpa only [heq, Pi.zero_apply, Pi.one_apply, MeasureTheory.volume_pi] using h

theorem tail_injOn (d : ℕ) : Set.InjOn (Duffy.tail d) (DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d) := by
  rw [tail_eq_comp]
  exact (tailAffine_injective d).injOn.comp (DuffyDomain.IntegrationConstruction.Duffy.front_injOn d) (mapsTo_image _ _)

theorem signed_tail_det (d : ℕ) (t : Fin d → ℝ) (ht : t ∈ DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d) :
    (-1 : ℝ) ^ d * (fderiv ℝ (Duffy.tail d) t).toLinearMap.det =
      |(fderiv ℝ (Duffy.tail d) t).toLinearMap.det| := by
  have hsign : (-1 : ℝ) ^ d * (-1 : ℝ) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  rw [fderiv_tail_det, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul, ← mul_assoc, hsign,
    abs_of_pos (DuffyDerivative.IntegrationConstruction.Duffy.fderiv_front_det_pos d t ht)]

theorem signed_integral_tail (d : ℕ) (g : (Fin d → ℝ) → ℂ) :
    (-1 : ℝ) ^ d •
      (∫ t in Icc (0 : Fin d → ℝ) 1,
        (fderiv ℝ (Duffy.tail d) t).toLinearMap.det • g (Duffy.tail d t)) =
      ∫ x in Duffy.tail d '' DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d, g x := by
  rw [← setIntegral_congr_set (cubeInterior_ae_eq_Icc d)]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (cubeInterior_isOpen d).measurableSet
    (fun t _ => (tail_hasFDerivAt d t).hasFDerivWithinAt) (tail_injOn d) g]
  rw [← integral_smul]
  apply setIntegral_congr_fun (cubeInterior_isOpen d).measurableSet
  intro t ht
  dsimp only
  rw [smul_smul, signed_tail_det d t ht]
  rw [(tail_hasFDerivAt d t).fderiv]

theorem signed_integral_simplex (d : ℕ) (g : (Fin d → ℝ) → ℂ) :
    (-1 : ℝ) ^ d •
      (∫ t in Icc (0 : Fin d → ℝ) 1,
        (fderiv ℝ (Duffy.tail d) t).toLinearMap.det • g (Duffy.tail d t)) =
      ∫ x in DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d, g x := by
  rw [signed_integral_tail, tail_image]

end

end OAI.AlgebraicTopology.FundamentalClass.IntegrationDuffyOrientation.Construction.Duffy
