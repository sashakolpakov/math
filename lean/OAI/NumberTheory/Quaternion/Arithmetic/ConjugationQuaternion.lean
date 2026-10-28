import OAI.NumberTheory.Quaternion.Arithmetic.Norm
import OAI.NumberTheory.Quaternion.Arithmetic.OrthogonalVector

/-! # Conjugation Quaternion -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ConjugationQuaternion

noncomputable section

section

/-! Every element of a nondegenerate quaternion algebra is conjugate
to its canonical conjugate by an explicitly constructed unit. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra

variable {F : Type*} [Field F] [CharZero F]

theorem quaternion_exists_star_intertwining_unit (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (q : ℍ[F,a,b]) : ∃ v : ℍ[F,a,b]ˣ, v.val * q = star q * v.val := by
  obtain ⟨s, t, u, horth, hnorm⟩ := OrthogonalVector.quaternion_exists_orthogonal_nonzero_norm a b ha hb q.imI q.imJ q.imK
  let w : ℍ[F,a,b] := ⟨0, s, t, u⟩
  have hw : Norm.quaternionNorm a b w ≠ 0 := by
    simpa only [Norm.quaternionNorm_formula, w, zero_pow (by omega : 2 ≠ 0), zero_sub, neg_mul] using hnorm
  refine ⟨Norm.quaternionUnitOfNormNeZero a b w hw, ?_⟩
  change w * q = star q * w
  apply QuaternionAlgebra.ext
  · simp only [w, re_mul, re_star, imI_star, imJ_star, imK_star]
    linear_combination 2 * horth
  · simp [w]
    ring
  · simp [w]
    ring
  · simp [w]
    ring

omit [CharZero F] in
theorem quaternionNorm_add_one (a b : F) (q : ℍ[F,a,b]) :
    Norm.quaternionNorm a b (q + 1) = Norm.quaternionNorm a b q + 2 * q.re + 1 := by
  simp only [Norm.quaternionNorm_formula, re_add, imI_add, imJ_add, imK_add,
    re_one, imI_one, imJ_one, imK_one]
  ring

omit [CharZero F] in
theorem quaternionNorm_neg (a b : F) (q : ℍ[F,a,b]) :
    Norm.quaternionNorm a b (-q) = Norm.quaternionNorm a b q := by
  simp only [Norm.quaternionNorm_formula, re_neg, imI_neg, imJ_neg, imK_neg, neg_sq]

end

section

/-! The reduced-norm-one subgroup of a quaternion algebra is generated
by ambient multiplicative commutators, over any characteristic-zero
field. Split and division quaternion algebras are treated together. -/

open scoped Classical _root_.Quaternion commutatorElement
open QuaternionAlgebra

theorem eq_commutator_of_intertwining {H : Type*} [Group H] {g u v : H}
    (h : u * v = g * (v * u)) : g = ⁅u, v⁆ := by
  calc
    g = (u * v) * (v * u)⁻¹ := (eq_mul_inv_iff_mul_eq).mpr h.symm
    _ = ⁅u, v⁆ := by simp only [mul_inv_rev, commutatorElement_def, mul_assoc]

variable {F : Type*} [Field F] [CharZero F]

theorem quaternion_norm_one_mem_commutator_of_add_one (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (q : ℍ[F,a,b]ˣ) (hq : Norm.quaternionNorm a b q.val = 1)
    (hplus : Norm.quaternionNorm a b (q.val + 1) ≠ 0) : q ∈ commutator ℍ[F,a,b]ˣ := by
  let u := Norm.quaternionUnitOfNormNeZero a b (q.val + 1) hplus
  obtain ⟨v, hv⟩ := quaternion_exists_star_intertwining_unit a b ha hb (q.val + 1)
  have hqstar : q.val * star (q.val + 1) = q.val + 1 := by
    rw [star_add, star_one, mul_add, Norm.quaternion_mul_star, hq, coe_one, mul_one, add_comm]
  have he : u * v = q * (v * u) := by
    apply Units.ext
    change (q.val + 1) * v.val = q.val * (v.val * (q.val + 1))
    rw [hv, ← mul_assoc, hqstar]
  rw [eq_commutator_of_intertwining he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)

omit [CharZero F] in
theorem quaternion_neg_one_mem_commutator (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (-1 : ℍ[F,a,b]ˣ) ∈ commutator ℍ[F,a,b]ˣ := by
  let x : ℍ[F,a,b] := ⟨0, 1, 0, 0⟩
  let y : ℍ[F,a,b] := ⟨0, 0, 1, 0⟩
  have hx : Norm.quaternionNorm a b x ≠ 0 := by
    simpa [Norm.quaternionNorm_formula, x] using neg_ne_zero.mpr ha
  have hy : Norm.quaternionNorm a b y ≠ 0 := by
    simpa [Norm.quaternionNorm_formula, y] using neg_ne_zero.mpr hb
  let u := Norm.quaternionUnitOfNormNeZero a b x hx
  let v := Norm.quaternionUnitOfNormNeZero a b y hy
  have he : u * v = (-1 : ℍ[F,a,b]ˣ) * (v * u) := by
    apply Units.ext
    change x * y = (-1 : ℍ[F,a,b]) * (y * x)
    apply QuaternionAlgebra.ext <;> simp [x, y]
  rw [eq_commutator_of_intertwining he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v)

theorem quaternion_norm_one_mem_commutator (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (q : ℍ[F,a,b]ˣ) (hq : Norm.quaternionNorm a b q.val = 1) : q ∈ commutator ℍ[F,a,b]ˣ := by
  by_cases hplus : Norm.quaternionNorm a b (q.val + 1) = 0
  · have hn : Norm.quaternionNorm a b (-q).val = 1 := by
      change Norm.quaternionNorm a b (-q.val) = 1
      rw [quaternionNorm_neg, hq]
    have hnplus : Norm.quaternionNorm a b ((-q).val + 1) ≠ 0 := by
      change Norm.quaternionNorm a b (-q.val + 1) ≠ 0
      have h₁ := quaternionNorm_add_one a b q.val
      have h₂ := quaternionNorm_add_one a b (-q.val)
      rw [hplus, hq] at h₁
      rw [quaternionNorm_neg, hq, re_neg] at h₂
      have he : Norm.quaternionNorm a b (-q.val + 1) = 4 := by linear_combination h₁ + h₂
      rw [he]
      norm_num
    have hm := (commutator ℍ[F,a,b]ˣ).mul_mem (quaternion_neg_one_mem_commutator a b ha hb)
      (quaternion_norm_one_mem_commutator_of_add_one a b ha hb (-q) hn hnplus)
    simpa using hm
  · exact quaternion_norm_one_mem_commutator_of_add_one a b ha hb q hq hplus

theorem quaternionUnitNorm_ker_le_commutator (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Norm.quaternionUnitNorm a b).ker ≤ commutator ℍ[F,a,b]ˣ := by
  intro q hq
  apply quaternion_norm_one_mem_commutator a b ha hb q
  exact congrArg Units.val (MonoidHom.mem_ker.mp hq)

end

/-! Entrywise scalar extension of quaternion algebras, including
compatibility with reduced norm and the canonical four-element basis. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra

variable {F K : Type*} [Field F] [Field K]

def quaternionCoefficientMap (ρ : F →+* K) (a b : F) : ℍ[F,a,b] →+* ℍ[K,ρ a,ρ b] where
  toFun q := ⟨ρ q.re, ρ q.imI, ρ q.imJ, ρ q.imK⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

theorem quaternionCoefficientMap_injective (ρ : F →+* K) (a b : F) :
    Function.Injective (quaternionCoefficientMap ρ a b) := by
  intro q r h
  apply QuaternionAlgebra.ext
  · exact ρ.injective (congrArg QuaternionAlgebra.re h)
  · exact ρ.injective (congrArg QuaternionAlgebra.imI h)
  · exact ρ.injective (congrArg QuaternionAlgebra.imJ h)
  · exact ρ.injective (congrArg QuaternionAlgebra.imK h)

theorem quaternionCoefficientMap_norm (ρ : F →+* K) (a b : F) (q : ℍ[F,a,b]) :
    Norm.quaternionNorm (ρ a) (ρ b) (quaternionCoefficientMap ρ a b q) = ρ (Norm.quaternionNorm a b q) := by
  simp [Norm.quaternionNorm_formula, quaternionCoefficientMap]

theorem quaternionCoefficientMap_basis (ρ : F →+* K) (a b : F) (j : Fin 4) :
    quaternionCoefficientMap ρ a b (basisOneIJK a 0 b j) = basisOneIJK (ρ a) 0 (ρ b) j := by
  simp only [basisOneIJK, Module.Basis.coe_ofEquivFun]
  apply QuaternionAlgebra.ext <;>
    simp [quaternionCoefficientMap, coe_linearEquivTuple_symm, equivTuple, Pi.single_apply]

variable [Algebra F K]

def quaternionCoefficientAlgHom (a b : F) :
    ℍ[F,a,b] →ₐ[F] ℍ[K,algebraMap F K a,algebraMap F K b] where
  __ := quaternionCoefficientMap (algebraMap F K) a b
  commutes' x := by
    change (⟨algebraMap F K x, algebraMap F K 0, algebraMap F K 0, algebraMap F K 0⟩ :
      ℍ[K,algebraMap F K a,algebraMap F K b]) = ⟨algebraMap F K x, 0, 0, 0⟩
    simp

end

end OAI.NumberTheory.Quaternion.Arithmetic.ConjugationQuaternion
