import OAI.AlgebraicGeometry.GroupSchemes.Verschiebung

/-! # Surjective -/

namespace OAI.AlgebraicGeometry.GroupSchemes.Surjective.FiniteEtaleV

noncomputable section

/-! Surjectivity criteria for the constructed Verschiebung. -/

open WithConv OAI.AlgebraicGeometry.GroupSchemes.Verschiebung.FiniteEtale

universe u
variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convAlgebra

/-- Verschiebung acts on the augmentation through inverse Frobenius. -/
theorem counit_verschiebung (x : A) :
    Coalgebra.counit (R := k) (Verschiebung.FiniteEtale.verschiebungFun p k A x) =
      (frobeniusEquiv k p).symm (Coalgebra.counit (R := k) x) := by
  have h := Verschiebung.FiniteEtale.eval_verschiebung p k A (1 : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) x
  simpa only [one_pow, LinearMap.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply] using h

/-- The constructed ring map is semilinear on scalars. -/
theorem verschiebung_scalars (c : k) :
    Verschiebung.FiniteEtale.verschiebungRingHom p k A (algebraMap k A c) =
      algebraMap k A ((frobeniusEquiv k p).symm c) := by
  have h := (Verschiebung.FiniteEtale.verschiebung p k A).map_smulₛₗ c (1 : A)
  change Verschiebung.FiniteEtale.verschiebungFun p k A (c • (1 : A)) =
    (frobeniusEquiv k p).symm c • Verschiebung.FiniteEtale.verschiebungFun p k A 1 at h
  change Verschiebung.FiniteEtale.verschiebungFun p k A (algebraMap k A c) = _
  simpa only [Algebra.smul_def, mul_one, Verschiebung.FiniteEtale.verschiebung_one] using h

/-- In finite dimension the semilinear ring map is a finite ring homomorphism. -/
theorem verschiebung_finite : (Verschiebung.FiniteEtale.verschiebungRingHom p k A).Finite := by
  apply RingHom.Finite.of_comp_finite (f := algebraMap k A)
  have he : (Verschiebung.FiniteEtale.verschiebungRingHom p k A).comp (algebraMap k A) =
      (algebraMap k A).comp (frobeniusEquiv k p).symm.toRingHom := by
    ext c
    exact verschiebung_scalars k A p c
  rw [he]
  exact (RingHom.finite_algebraMap.mpr inferInstance).comp (frobeniusEquiv k p).symm.finite

/-- Reduced Cartier-dual coordinates make Verschiebung surjective. -/
theorem verschiebung_surjective [IsReduced (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)] :
    Function.Surjective (Verschiebung.FiniteEtale.verschiebungFun p k A) := by
  have : RingHomSurjective (frobeniusEquiv k p).symm.toRingHom :=
    ⟨(frobeniusEquiv k p).symm.surjective⟩
  change Function.Surjective (Verschiebung.FiniteEtale.verschiebung p k A)
  apply LinearMap.range_eq_top.mp
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro f hf
  have hp : (toConv f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) ^ p = 0 := by
    ext x
    rw [← Verschiebung.FiniteEtale.eval_verschiebung_pow]
    have hfx : f (Verschiebung.FiniteEtale.verschiebungFun p k A x) = 0 :=
      (Submodule.mem_dualAnnihilator f).mp hf _ ⟨x, rfl⟩
    rw [hfx, zero_pow (Fact.out : p.Prime).ne_zero]
    rfl
  have hnil : IsNilpotent (toConv f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := ⟨p, hp⟩
  have hz : (toConv f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) = 0 := hnil.eq_zero
  exact WithConv.toConv_injective hz

/-- Surjectivity of Verschiebung forces reduced Cartier-dual coordinates. -/
theorem dual_reduced_of_surjective (hV : Function.Surjective (Verschiebung.FiniteEtale.verschiebungFun p k A)) :
    IsReduced (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := by
  have hF : ∀ f : AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A, f ^ p = 0 → f = 0 := by
    intro f hf
    ext x
    obtain ⟨y, rfl⟩ := hV x
    have he := Verschiebung.FiniteEtale.eval_verschiebung_pow p k A f y
    rw [hf] at he
    exact eq_zero_of_pow_eq_zero he
  constructor
  intro f hf
  obtain ⟨n, hn⟩ := hf
  have hnp : n ≤ p ^ n := by
    clear hn
    have hp := (Fact.out : p.Prime).two_le
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have hpos : 0 < p ^ n := pow_pos (by omega) n
      nlinarith
  have hzero := pow_eq_zero_of_le hnp hn
  clear hn hnp
  induction n with
  | zero => simpa only [pow_zero, pow_one] using hzero
  | succ n ih =>
    apply ih
    apply hF
    simpa only [← pow_mul, pow_succ] using hzero

end

end OAI.AlgebraicGeometry.GroupSchemes.Surjective.FiniteEtaleV
