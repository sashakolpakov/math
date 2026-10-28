import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Instances.AddCircle.Real

/-! # Torsion Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion

noncomputable section

section

/-! Actual torsion groups of real tori. The standard coefficient groups
are constructed through lattice coordinates, including composite levels. -/

open scoped Classical

def killedBy (G : Type*) [AddCommGroup G] (N : ℕ) : AddSubgroup G :=
  (nsmulAddMonoidHom (α := G) N).ker

def circleMap (N : ℕ) [NeZero N] : ZMod N →+ killedBy UnitAddCircle N where
  toFun x := ⟨ZMod.toAddCircle x, by
    change N • ZMod.toAddCircle x = 0
    rw [← map_nsmul, nsmul_eq_mul]
    simp⟩
  map_zero' := Subtype.ext (map_zero ZMod.toAddCircle)
  map_add' x y := Subtype.ext (map_add ZMod.toAddCircle x y)

theorem circleMap_bijective (N : ℕ) [NeZero N] : Function.Bijective (circleMap N) := by
  constructor
  · intro x y h
    exact ZMod.toAddCircle_injective N (congrArg Subtype.val h)
  · intro x
    have hx : N • x.val = 0 := x.property
    obtain ⟨m, _, hm⟩ := (AddCircle.nsmul_eq_zero_iff (Nat.pos_of_ne_zero (NeZero.ne N))).mp hx
    refine ⟨(m : ZMod N), Subtype.ext ?_⟩
    change ZMod.toAddCircle (m : ZMod N) = x.val
    rw [ZMod.toAddCircle_natCast]
    simpa only [mul_one] using hm

/-- The actual N-torsion of the real circle is cyclic of order N. -/
def circleEquiv (N : ℕ) [NeZero N] : ZMod N ≃+ killedBy UnitAddCircle N :=
  AddEquiv.ofBijective (circleMap N) (circleMap_bijective N)

def killedByEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (N : ℕ) : killedBy G N ≃+ killedBy H N where
  toFun x := ⟨e x.val, by
    change N • e x.val = 0
    rw [← map_nsmul, show N • x.val = 0 from x.property, map_zero]⟩
  invFun x := ⟨e.symm x.val, by
    change N • e.symm x.val = 0
    rw [← map_nsmul, show N • x.val = 0 from x.property, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)

def piKilledByEquiv (I : Type*) (G : I → Type*) [∀ i, AddCommGroup (G i)] (N : ℕ) :
    killedBy (∀ i, G i) N ≃+ ∀ i, killedBy (G i) N where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, funext fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Torsion of a product of real circles has its ordered standard basis. -/
def piCircleEquiv (I : Type*) (N : ℕ) [NeZero N] :
    (I → ZMod N) ≃+ killedBy (I → UnitAddCircle) N :=
  (AddEquiv.piCongrRight (fun _ : I => circleEquiv N)).trans
    (piKilledByEquiv I (fun _ => UnitAddCircle) N).symm

section Coordinates

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I]
  (b : Module.Basis I ℝ V)

def coordinateMap : V →+ (I → UnitAddCircle) where
  toFun x i := (b.equivFun x i : UnitAddCircle)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

theorem coordinateMap_surjective : Function.Surjective (coordinateMap b) := by
  intro x
  have hs : Function.Surjective (fun y : ℝ => (y : UnitAddCircle)) :=
    QuotientAddGroup.mk_surjective
  choose y hy using fun i => hs (x i)
  refine ⟨b.equivFun.symm y, ?_⟩
  ext i
  change (b.equivFun (b.equivFun.symm y) i : UnitAddCircle) = x i
  rw [b.equivFun.apply_symm_apply]
  exact hy i

theorem coordinateMap_ker : (coordinateMap b).ker =
    (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
  ext x
  change coordinateMap b x = 0 ↔ x ∈ Submodule.span ℤ (Set.range b)
  rw [b.mem_span_iff_repr_mem ℤ x]
  constructor
  · intro h i
    have hi : (b.equivFun x i : UnitAddCircle) = 0 := congrFun h i
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
    refine ⟨n, ?_⟩
    change (n : ℝ) = b.repr x i
    simpa only [zsmul_eq_mul, mul_one, b.equivFun_apply] using hn
  · intro h
    ext i
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    obtain ⟨n, hn⟩ := h i
    change (n : ℝ) = b.repr x i at hn
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one, b.equivFun_apply] using hn⟩

/-- Lattice coordinates identify the actual quotient group with a
product of real circles. -/
def basisTorusEquiv :
    (V ⧸ (Submodule.span ℤ (Set.range b)).toAddSubgroup) ≃+ (I → UnitAddCircle) :=
  (QuotientAddGroup.quotientAddEquivOfEq (coordinateMap_ker b)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (coordinateMap b) (coordinateMap_surjective b))

end Coordinates

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  [Fintype I] (b : Module.Basis I ℤ Λ)

/-- An integral basis gives the standard torsion group of the actual
torus quotient. This applies uniformly to every positive integer N. -/
def latticeTorsionEquiv (N : ℕ) [NeZero N] :
    (I → ZMod N) ≃+ killedBy (V ⧸ Λ.toAddSubgroup) N := by
  let B := b.ofZLatticeBasis ℝ Λ
  let e : (V ⧸ Λ.toAddSubgroup) ≃+ (I → UnitAddCircle) :=
    (QuotientAddGroup.quotientAddEquivOfEq
      (congrArg Submodule.toAddSubgroup (b.ofZLatticeBasis_span ℝ Λ))).symm.trans
        (basisTorusEquiv B)
  exact (piCircleEquiv I N).trans (killedByEquiv e N).symm

end

/-! Fixing the actual N-torsion of a lattice quotient is exactly the
principal congruence condition on its integral lattice. -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (Λ : Submodule ℤ V)
  (N : ℕ) [NeZero N]

theorem nat_smul_inverse (v : V) : N • ((N : ℚ)⁻¹ • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀]
  · exact one_smul ℚ v
  · exact_mod_cast NeZero.ne N

theorem inverse_smul_nat (v : V) : (N : ℚ)⁻¹ • (N • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀]
  · exact one_smul ℚ v
  · exact_mod_cast NeZero.ne N

/-- The N-division point associated with an actual integral period. -/
def latticeDivisionPoint (v : Λ) : killedBy (V ⧸ Λ.toAddSubgroup) N :=
  ⟨QuotientAddGroup.mk ((N : ℚ)⁻¹ • v.val), by
    change N • (QuotientAddGroup.mk ((N : ℚ)⁻¹ • v.val) : V ⧸ Λ.toAddSubgroup) = 0
    rw [← QuotientAddGroup.mk_nsmul, nat_smul_inverse]
    exact (QuotientAddGroup.eq_zero_iff v.val).mpr v.property⟩

theorem latticeDivisionPoint_surjective : Function.Surjective (latticeDivisionPoint Λ N) := by
  intro x
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective x.val
  have hNv : N • v ∈ Λ := by
    change N • v ∈ Λ.toAddSubgroup
    apply (QuotientAddGroup.eq_zero_iff (N • v)).mp
    rw [QuotientAddGroup.mk_nsmul, hv]
    exact x.property
  refine ⟨⟨N • v, hNv⟩, Subtype.ext ?_⟩
  change (QuotientAddGroup.mk ((N : ℚ)⁻¹ • (N • v)) : V ⧸ Λ.toAddSubgroup) = x.val
  rw [inverse_smul_nat, hv]

def quotientLinearMap (f : V →ₗ[ℚ] V) (hf : ∀ v ∈ Λ, f v ∈ Λ) :
    (V ⧸ Λ.toAddSubgroup) →+ (V ⧸ Λ.toAddSubgroup) :=
  QuotientAddGroup.map Λ.toAddSubgroup Λ.toAddSubgroup f.toAddMonoidHom hf

/-- Torsion points are fixed precisely when every lattice vector is
fixed modulo N times the very same lattice. -/
theorem fixes_torsion_iff_congruence (f : V →ₗ[ℚ] V) (hf : ∀ v ∈ Λ, f v ∈ Λ) :
    (∀ x : killedBy (V ⧸ Λ.toAddSubgroup) N, quotientLinearMap Λ f hf x.val = x.val) ↔
      ∀ v ∈ Λ, ∃ w ∈ Λ, f v - v = (N : ℤ) • w := by
  constructor
  · intro h v hv
    have he := h (latticeDivisionPoint Λ N ⟨v, hv⟩)
    have hw : (N : ℚ)⁻¹ • (f v - v) ∈ Λ := by
      have hm : f ((N : ℚ)⁻¹ • v) - (N : ℚ)⁻¹ • v ∈ Λ :=
        QuotientAddGroup.eq_iff_sub_mem.mp he
      simpa only [map_smul, smul_sub] using hm
    refine ⟨(N : ℚ)⁻¹ • (f v - v), hw, ?_⟩
    exact (nat_smul_inverse N (f v - v)).symm.trans (natCast_zsmul _ _).symm
  · intro h x
    obtain ⟨v, rfl⟩ := latticeDivisionPoint_surjective Λ N x
    obtain ⟨w, hw, he⟩ := h v.val v.property
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    change f ((N : ℚ)⁻¹ • v.val) - (N : ℚ)⁻¹ • v.val ∈ Λ
    rw [map_smul, ← smul_sub, he, natCast_zsmul, inverse_smul_nat]
    exact hw

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion
