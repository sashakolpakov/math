import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingCocycleContraction

/-! # Jacobi Linearization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.JacobiLinearization.Construction

noncomputable section

/-! The Jacobi equations are quadratic in the bracket. Their
linearization at a Lie bracket is the second cochain differential. -/

open scoped Classical
open LieAlgebra LieModule.Cohomology

def jacobiPair {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B C : V →ₗ[k] V →ₗ[k] V) : V →ₗ[k] V →ₗ[k] V →ₗ[k] V where
  toFun x := {
    toFun y := {
      toFun z := B x (C y z) - B y (C x z) - B (C x y) z
      map_add' z w := by simp; abel
      map_smul' c z := by simp [smul_sub] }
    map_add' y z := by ext w; simp; abel
    map_smul' c y := by ext z; simp [smul_sub] }
  map_add' x y := by ext z w; simp; abel
  map_smul' c x := by ext y z; simp [smul_sub]

theorem jacobiPair_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B C : V →ₗ[k] V →ₗ[k] V) (x y z : V) :
    jacobiPair B C x y z = B x (C y z) - B y (C x z) - B (C x y) z := rfl

def jacobiBilinear {k V : Type*} [Field k] [AddCommGroup V] [Module k V] :
    (V →ₗ[k] V →ₗ[k] V) →ₗ[k] (V →ₗ[k] V →ₗ[k] V) →ₗ[k]
      V →ₗ[k] V →ₗ[k] V →ₗ[k] V where
  toFun B := {
    toFun C := jacobiPair B C
    map_add' C D := by
      ext x y z
      simp only [jacobiPair_apply, LinearMap.add_apply, map_add]
      abel
    map_smul' c C := by
      ext x y z
      simp [jacobiPair_apply, smul_sub] }
  map_add' B C := by
    ext D x y z
    simp [jacobiPair_apply]
    abel
  map_smul' c B := by
    ext C x y z
    simp [jacobiPair_apply, smul_sub]

def jacobiLinearization {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B : V →ₗ[k] V →ₗ[k] V) :
    (V →ₗ[k] V →ₗ[k] V) →ₗ[k] V →ₗ[k] V →ₗ[k] V →ₗ[k] V :=
  jacobiBilinear B + jacobiBilinear.flip B

theorem jacobi_perturbation
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (B C : V →ₗ[k] V →ₗ[k] V) :
    jacobiPair (B + C) (B + C) = jacobiPair B B + jacobiLinearization B C + jacobiPair C C := by
  change jacobiBilinear (B + C) (B + C) = _
  simp only [map_add, LinearMap.add_apply, jacobiLinearization, LinearMap.flip_apply]
  change jacobiPair B B + jacobiPair C B + (jacobiPair B C + jacobiPair C C) =
    jacobiPair B B + (jacobiPair B C + jacobiPair C B) + jacobiPair C C
  abel

attribute [local instance] LieRing.ofAssociativeRing

theorem jacobiPair_lie_self
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] :
    jacobiPair (ad k L).toLinearMap (ad k L).toLinearMap = 0 := by
  ext x y z
  change ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ - ⁅⁅x, y⁆, z⁆ = 0
  rw [leibniz_lie x y z]
  abel

theorem jacobiLinearization_eq_coboundary
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] (c : twoCochain k L L) :
    jacobiLinearization (ad k L).toLinearMap c.val = d₂₃ k L L c := by
  ext x y z
  change (⁅x, c y z⁆ - ⁅y, c x z⁆ - ⁅c x y, z⁆) +
      (c x ⁅y, z⁆ - c y ⁅x, z⁆ - c ⁅x, y⁆ z) = _
  rw [d₂₃_apply, ← lie_skew (c x y) z,
    ← twoCochain_skew c ⁅y, z⁆ x, ← twoCochain_skew c ⁅x, z⁆ y]
  abel

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.JacobiLinearization.Construction
