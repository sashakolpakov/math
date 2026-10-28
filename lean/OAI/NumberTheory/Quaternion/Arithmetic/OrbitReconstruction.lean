import OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

/-! # Orbit Reconstruction -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.OrbitReconstruction

noncomputable section

/-! A quaternion norm-one matrix is recovered linearly from its
value on any fixed quaternion unit. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra

variable {F K : Type} [Field F] [Field K]

def quaternionOrbitRecovery (a b : K) (r : ℍ[K,a,b]ˣ) :
    (Fin 4 → K) →ₗ[K] Matrix (Fin 4) (Fin 4) K where
  toFun x := MatrixQuaternionDet.quaternionRegularMatrix a b (MatrixGroup.quaternionOfCoordinates a b x * (r⁻¹).val)
  map_add' x y := by
    simp only [MatrixGroup.quaternionOfCoordinates, map_add, add_mul]
  map_smul' c x := by
    simp only [MatrixGroup.quaternionOfCoordinates, map_smul, Algebra.smul_mul_assoc, RingHom.id_apply]

theorem quaternionOrbitRecovery_apply (a b : F) (ρ : F →+* K)
    (r : ℍ[K,ρ a,ρ b]ˣ) (g : (MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ) :
    quaternionOrbitRecovery (ρ a) (ρ b) r
      (g.val.val *ᵥ linearEquivTuple (ρ a) 0 (ρ b) r.val) = g.val.val := by
  obtain ⟨q, rfl⟩ := (MatrixGroup.quaternionMatrixPointsEquiv a b ρ).surjective g
  change MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b)
    (MatrixGroup.quaternionOfCoordinates (ρ a) (ρ b)
      (MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) q.val.val *ᵥ
        linearEquivTuple (ρ a) 0 (ρ b) r.val) * (r⁻¹).val) = _
  rw [MatrixGroup.quaternionRegularMatrix_coordinates_mul]
  change MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b)
    ((q.val.val * (linearEquivTuple (ρ a) 0 (ρ b)).symm
      (linearEquivTuple (ρ a) 0 (ρ b) r.val)) * (r⁻¹).val) = _
  rw [LinearEquiv.symm_apply_apply, mul_assoc, Units.mul_inv, mul_one]
  rfl

theorem quaternion_normOne_inverse_star (a b : K) (q : (Norm.quaternionUnitNorm a b).ker) :
    q.val⁻¹.val = star q.val.val := by
  have hn : Norm.quaternionNorm a b q.val.val = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.mp q.property)
  have hstar : q.val.val * star q.val.val = 1 := by
    rw [Norm.quaternion_mul_star, hn, coe_one]
  exact left_inv_eq_right_inv q.val.inv_val hstar

def quaternionIntegralCoordinates (S : Subring K) (a b : K) (q : ℍ[K,a,b]) : Prop :=
  q.re ∈ S ∧ q.imI ∈ S ∧ q.imJ ∈ S ∧ q.imK ∈ S

theorem quaternionIntegralCoordinates_of_tuple (S : Subring K) (a b : K) (x : Fin 4 → K)
    (hx : ∀ i, x i ∈ S) : quaternionIntegralCoordinates S a b (MatrixGroup.quaternionOfCoordinates a b x) :=
  ⟨hx 0, hx 1, hx 2, hx 3⟩

theorem quaternionIntegralCoordinates_mul (S : Subring K) (a b : K) (ha : a ∈ S) (hb : b ∈ S)
    (q r : ℍ[K,a,b]) (hq : quaternionIntegralCoordinates S a b q)
    (hr : quaternionIntegralCoordinates S a b r) : quaternionIntegralCoordinates S a b (q * r) := by
  rcases hq with ⟨hq0, hq1, hq2, hq3⟩
  rcases hr with ⟨hr0, hr1, hr2, hr3⟩
  simp only [quaternionIntegralCoordinates, re_mul, imI_mul, imJ_mul, imK_mul, zero_mul,
    add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    aesop (add safe apply [S.add_mem, S.sub_mem, S.mul_mem])

theorem quaternionIntegralCoordinates_star (S : Subring K) (a b : K) (q : ℍ[K,a,b])
    (hq : quaternionIntegralCoordinates S a b q) : quaternionIntegralCoordinates S a b (star q) := by
  simpa only [quaternionIntegralCoordinates, re_star, imI_star, imJ_star, imK_star,
    zero_mul, add_zero] using
    (show q.re ∈ S ∧ -q.imI ∈ S ∧ -q.imJ ∈ S ∧ -q.imK ∈ S from
      ⟨hq.1, S.neg_mem hq.2.1, S.neg_mem hq.2.2.1, S.neg_mem hq.2.2.2⟩)

theorem quaternionRegularMatrix_integral (S : Subring K) (a b : K) (ha : a ∈ S) (hb : b ∈ S)
    (q : ℍ[K,a,b]) (hq : quaternionIntegralCoordinates S a b q) :
    ∀ i j, MatrixQuaternionDet.quaternionRegularMatrix a b q i j ∈ S := by
  rcases hq with ⟨hq0, hq1, hq2, hq3⟩
  rw [MatrixQuaternionDet.quaternionRegularMatrix_apply]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply] <;>
    aesop (add safe apply [S.mul_mem, S.neg_mem])

theorem quaternion_integral_of_integral_orbit (a b : F) (ρ : F →+* K) (S : Subring K)
    (ha : ρ a ∈ S) (hb : ρ b ∈ S) (r : ℍ[K,ρ a,ρ b]ˣ)
    (hr : quaternionIntegralCoordinates S (ρ a) (ρ b) (r⁻¹).val)
    (g : (MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ)
    (hg : ∀ i, (g.val.val *ᵥ linearEquivTuple (ρ a) 0 (ρ b) r.val) i ∈ S) :
    (∀ i j, g.val i j ∈ S) ∧ ∀ i j, (g⁻¹).val i j ∈ S := by
  obtain ⟨q, rfl⟩ := (MatrixGroup.quaternionMatrixPointsEquiv a b ρ).surjective g
  have hprod := quaternionIntegralCoordinates_of_tuple S (ρ a) (ρ b) _ hg
  have hq := quaternionIntegralCoordinates_mul S (ρ a) (ρ b) ha hb _ _ hprod hr
  change quaternionIntegralCoordinates S (ρ a) (ρ b)
    (MatrixGroup.quaternionOfCoordinates (ρ a) (ρ b)
      (MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) q.val.val *ᵥ
        linearEquivTuple (ρ a) 0 (ρ b) r.val) * (r⁻¹).val) at hq
  rw [MatrixGroup.quaternionRegularMatrix_coordinates_mul] at hq
  change quaternionIntegralCoordinates S (ρ a) (ρ b)
    ((q.val.val * (linearEquivTuple (ρ a) 0 (ρ b)).symm
      (linearEquivTuple (ρ a) 0 (ρ b) r.val)) * (r⁻¹).val) at hq
  rw [LinearEquiv.symm_apply_apply, mul_assoc, Units.mul_inv, mul_one] at hq
  refine ⟨quaternionRegularMatrix_integral S (ρ a) (ρ b) ha hb _ hq, ?_⟩
  rw [← map_inv]
  change ∀ i j, MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) (q.val⁻¹).val i j ∈ S
  rw [quaternion_normOne_inverse_star]
  exact quaternionRegularMatrix_integral S (ρ a) (ρ b) ha hb _
    (quaternionIntegralCoordinates_star S (ρ a) (ρ b) _ hq)

end

end OAI.NumberTheory.Quaternion.Arithmetic.OrbitReconstruction
