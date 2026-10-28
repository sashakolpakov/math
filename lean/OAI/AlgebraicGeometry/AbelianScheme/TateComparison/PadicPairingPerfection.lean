import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueLimit
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # Padic Pairing Perfection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicPairingPerfection

noncomputable section

section

/-! A finite free integral p-adic pairing is perfect once its matrix
is nonsingular modulo p. This lifts finite-level perfection without
assuming an integral dual-lattice identity. -/

variable (q : ℕ) [Fact q.Prime]

theorem padic_isUnit_of_residue_ne_zero (x : ℤ_[q]) (hx : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra h
  apply hx
  apply RingHom.mem_ker.mp
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact h

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem padic_matrix_det_unit_of_residue (M : Matrix I I ℤ_[q])
    (h : ((PadicInt.toZMod (p := q)).mapMatrix M).det ≠ 0) : IsUnit M.det := by
  apply padic_isUnit_of_residue_ne_zero q
  exact (PadicInt.toZMod (p := q)).map_det M ▸ h

section LinearMap
variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem linearMap_bijective_of_unit_matrix
    (bV : Module.Basis I R V) (bW : Module.Basis I R W) (f : V →ₗ[R] W)
    (hf : IsUnit (LinearMap.toMatrix bV bW f).det) : Function.Bijective f := by
  let M := LinearMap.toMatrix bV bW f
  let g := Matrix.toLin bW bV M⁻¹
  have hfg : f.comp g = LinearMap.id := by
    rw [← Matrix.toLin_toMatrix bV bW f]
    change (Matrix.toLin bV bW M).comp (Matrix.toLin bW bV M⁻¹) = _
    rw [← Matrix.toLin_mul bW bV bW, Matrix.mul_nonsing_inv M hf, Matrix.toLin_one]
  have hgf : g.comp f = LinearMap.id := by
    rw [← Matrix.toLin_toMatrix bV bW f]
    change (Matrix.toLin bW bV M⁻¹).comp (Matrix.toLin bV bW M) = _
    rw [← Matrix.toLin_mul bV bW bV, Matrix.nonsing_inv_mul M hf, Matrix.toLin_one]
  have hleft : Function.LeftInverse g f := fun x => LinearMap.congr_fun hgf x
  have hright : Function.RightInverse g f := fun x => LinearMap.congr_fun hfg x
  exact ⟨hleft.injective, hright.surjective⟩

end LinearMap

variable {V W : Type*} [AddCommGroup V] [Module ℤ_[q] V]
  [AddCommGroup W] [Module ℤ_[q] W]

theorem padic_pairing_perfect_of_residue_det
    (bV : Module.Basis I ℤ_[q] V) (bW : Module.Basis I ℤ_[q] W)
    (B : V →ₗ[ℤ_[q]] W →ₗ[ℤ_[q]] ℤ_[q])
    (h : ((PadicInt.toZMod (p := q)).mapMatrix (LinearMap.toMatrix bV bW.dualBasis B)).det ≠ 0) :
    B.IsPerfPair := by
  have : Module.Free ℤ_[q] W := Module.Free.of_basis bW
  have : Module.Finite ℤ_[q] W := Module.Finite.of_basis bW
  exact LinearMap.IsPerfPair.of_bijective B
    (linearMap_bijective_of_unit_matrix bV bW.dualBasis B
      (padic_matrix_det_unit_of_residue q _ h))

end

/-! Detection modulo q forces a square integral p-adic pairing matrix
to have unit determinant, hence gives an actual perfect pairing. -/

open scoped BigOperators

variable (q : ℕ) [Fact q.Prime] {I : Type*} [Fintype I] [DecidableEq I]
  {V W : Type*} [AddCommGroup V] [Module ℤ_[q] V] [AddCommGroup W] [Module ℤ_[q] W]

theorem padic_matrix_residue_det_ne_zero_of_kernel
    (bV : Module.Basis I ℤ_[q] V) (bW : Module.Basis I ℤ_[q] W) (f : V →ₗ[ℤ_[q]] W)
    (hf : ∀ x, (∀ i, PadicInt.toZMod (bW.repr (f x) i) = 0) → ∃ y, (q : ℤ_[q]) • y = x) :
    ((PadicInt.toZMod (p := q)).mapMatrix (LinearMap.toMatrix bV bW f)).det ≠ 0 := by
  intro hdet
  let M := LinearMap.toMatrix bV bW f
  let r := PadicInt.toZMod (p := q)
  obtain ⟨a, ha, hMa⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := r.mapMatrix M)).mpr hdet
  let c : I → ℤ_[q] := fun i => (a i).val
  have hc (i : I) : r (c i) = a i := by
    exact (map_natCast r (a i).val).trans (ZMod.natCast_zmod_val (a i))
  let x := bV.equivFun.symm c
  have hx : (bV.repr x : I → ℤ_[q]) = c := bV.equivFun.apply_symm_apply c
  have hfx : (bW.repr (f x) : I → ℤ_[q]) = M.mulVec c := by
    rw [← LinearMap.toMatrix_mulVec_repr bV bW f x, hx]
  have hzero (i : I) : r (bW.repr (f x) i) = 0 := by
    rw [congrFun hfx i, RingHom.map_mulVec]
    have hrc : r ∘ c = a := funext hc
    rw [hrc]
    exact congrFun hMa i
  obtain ⟨y, hy⟩ := hf x hzero
  apply ha
  funext i
  have hci : c i = (q : ℤ_[q]) * bV.repr y i := by
    rw [← congrFun hx i, ← hy, map_smul]
    rfl
  exact (hc i).symm.trans (by
    rw [hci, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
    rfl)

theorem padic_pairing_perfect_of_reduction_detection
    (bV : Module.Basis I ℤ_[q] V) (bW : Module.Basis I ℤ_[q] W)
    (B : V →ₗ[ℤ_[q]] W →ₗ[ℤ_[q]] ℤ_[q])
    (hB : ∀ x, (∀ y, PadicInt.toZMod (B x y) = 0) → ∃ z, (q : ℤ_[q]) • z = x) :
    B.IsPerfPair := by
  apply padic_pairing_perfect_of_residue_det q bV bW B
  apply padic_matrix_residue_det_ne_zero_of_kernel q bV bW.dualBasis B
  intro x hx
  apply hB x
  intro y
  have hbase (i : I) : PadicInt.toZMod (B x (bW i)) = 0 := by
    simpa only [Module.Basis.dualBasis_repr] using hx i
  rw [← bW.sum_repr y, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  change PadicInt.toZMod (bW.repr y i * B x (bW i)) = 0
  rw [map_mul, hbase, mul_zero]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicPairingPerfection
