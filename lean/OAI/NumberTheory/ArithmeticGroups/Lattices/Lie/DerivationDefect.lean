import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.KillingForm
import Mathlib.Algebra.Lie.Derivation.Killing

/-! # Derivation Defect -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.DerivationDefect.Construction

noncomputable section

section

/-! The real Minkowski Lie space is a Killing Lie algebra, and every
one of its derivations is an intrinsic adjoint operator. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing

def lieMixedRealSubalgebra
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    LieSubalgebra ℝ (Matrix (Fin n) (Fin n) (mixedSpace k)) where
  toSubmodule := MixedLattice.Construction.lieMixedSpan G
  lie_mem' := fun {_ _} hA hB => Minkowski.LieBracket.Construction.lieMixedSpan_commutator_mem G hG hA hB

theorem lieMixed_isKilling
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LieAlgebra.IsKilling ℝ (lieMixedRealSubalgebra G hG) := by
  have hB : (killingForm ℝ (lieMixedRealSubalgebra G hG)).Nondegenerate := Minkowski.KillingForm.Construction.lieMixedKillingForm_nondegenerate G hG hsemi
  constructor
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  exact hB.2 x (fun y => hx y (LieSubmodule.mem_top y))

theorem lieMixed_derivation_is_inner
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (D : LieDerivation ℝ (lieMixedRealSubalgebra G hG) (lieMixedRealSubalgebra G hG)) :
    ∃ A : MixedLattice.Construction.lieMixedSpan G, D.toLinearMap = Minkowski.AdjointOperator.Construction.lieMixedAdjoint G hG A := by
  let : LieAlgebra.IsKilling ℝ (lieMixedRealSubalgebra G hG) := lieMixed_isKilling G hG hsemi
  obtain ⟨A, hA⟩ := LieDerivation.IsKilling.exists_eq_ad D
  refine ⟨A, ?_⟩
  have he : (LieDerivation.ad ℝ (lieMixedRealSubalgebra G hG) A :
      Module.End ℝ (lieMixedRealSubalgebra G hG)) = D.toLinearMap :=
    congrArg LieDerivation.toLinearMap hA
  rw [LieDerivation.coe_ad_apply_eq_ad_apply] at he
  exact he.symm

end

/-! The linearized bracket-preservation equations have precisely the inner
derivations as their kernel for the real Minkowski Lie algebra. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

attribute [local instance] LieRing.ofAssociativeRing

def lieDerivationDefect (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] :
    Module.End R L →ₗ[R] (L →ₗ[R] L →ₗ[R] L) where
  toFun T :=
    (LieAlgebra.ad R L).toLinearMap.compr₂ T -
      (LieAlgebra.ad R L).toLinearMap.compl₁₂ T LinearMap.id -
      (LieAlgebra.ad R L).toLinearMap.compl₁₂ LinearMap.id T
  map_add' T S := by
    ext x y
    change (T + S) ⁅x, y⁆ - ⁅(T + S) x, y⁆ - ⁅x, (T + S) y⁆ =
      (T ⁅x, y⁆ - ⁅T x, y⁆ - ⁅x, T y⁆) + (S ⁅x, y⁆ - ⁅S x, y⁆ - ⁅x, S y⁆)
    simp only [LinearMap.add_apply, add_lie, lie_add]
    abel
  map_smul' c T := by
    ext x y
    change (c • T) ⁅x, y⁆ - ⁅(c • T) x, y⁆ - ⁅x, (c • T) y⁆ =
      c • (T ⁅x, y⁆ - ⁅T x, y⁆ - ⁅x, T y⁆)
    simp only [LinearMap.smul_apply, smul_lie, lie_smul, smul_sub]

theorem lieDerivationDefect_apply
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (T : Module.End R L) (x y : L) :
    lieDerivationDefect R L T x y = T ⁅x, y⁆ - ⁅T x, y⁆ - ⁅x, T y⁆ := rfl

theorem lieDerivationDefect_eq_zero_iff
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (T : Module.End R L) :
    lieDerivationDefect R L T = 0 ↔
      ∃ D : LieDerivation R L L, D.toLinearMap = T := by
  constructor
  · intro h
    refine ⟨{ toLinearMap := T, leibniz' := ?_ }, rfl⟩
    intro x y
    have he := DFunLike.congr_fun (DFunLike.congr_fun h x) y
    change T ⁅x, y⁆ - ⁅T x, y⁆ - ⁅x, T y⁆ = 0 at he
    rw [sub_eq_zero, sub_eq_iff_eq_add] at he
    rw [he, sub_eq_add_neg, lie_skew]
  · rintro ⟨D, rfl⟩
    ext x y
    change D ⁅x, y⁆ - ⁅D x, y⁆ - ⁅x, D y⁆ = 0
    rw [LieDerivation.apply_lie_eq_add]
    abel

theorem lieDerivationDefect_ad
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (A : L) :
    lieDerivationDefect R L (LieAlgebra.ad R L A) = 0 := by
  apply (lieDerivationDefect_eq_zero_iff _).mpr
  exact ⟨LieDerivation.ad R L A, LieDerivation.coe_ad_apply_eq_ad_apply A⟩

theorem lieDerivationDefect_of_bracket_preserving
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (T : Module.End R L)
    (hT : ∀ x y, (1 + T : Module.End R L) ⁅x, y⁆ =
      ⁅(1 + T : Module.End R L) x, (1 + T : Module.End R L) y⁆) (x y : L) :
    lieDerivationDefect R L T x y = ⁅T x, T y⁆ := by
  have he := hT x y
  simp only [LinearMap.add_apply, Module.End.one_apply, add_lie, lie_add] at he
  rw [lieDerivationDefect_apply]
  apply sub_eq_zero.mp
  calc
    _ = (⁅x, y⁆ + T ⁅x, y⁆) -
      (⁅x, y⁆ + ⁅T x, y⁆ + (⁅x, T y⁆ + ⁅T x, T y⁆)) := by abel
    _ = 0 := sub_eq_zero.mpr he

theorem lieMixed_derivationDefect_ker
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    LinearMap.ker (lieDerivationDefect ℝ (lieMixedRealSubalgebra G hG)) =
      LinearMap.range (Minkowski.AdjointOperator.Construction.lieMixedAdjointLinear G hG) := by
  ext T
  constructor
  · intro hT
    obtain ⟨D, hD⟩ := (lieDerivationDefect_eq_zero_iff T).mp hT
    obtain ⟨A, hA⟩ := lieMixed_derivation_is_inner G hG hsemi D
    exact ⟨A, hA.symm.trans hD⟩
  · rintro ⟨A, rfl⟩
    exact lieDerivationDefect_ad (R := ℝ) (L := lieMixedRealSubalgebra G hG) A

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.DerivationDefect.Construction
