import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedReverse

/-! # Reverse Sides -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The reverse map for an isogeny satisfies both multiplier equations.
Finite kernel and surjectivity supply a second inverse multiple, so no
surjectivity of the integral Tate map is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

namespace ReverseSides.Tate

universe u
variable (q : ℕ) [Fact q.Prime] {H H' : Type u} [AddCommGroup H] [AddCommGroup H']

theorem reverse_comp_symm (f : H →+ H') (hf : Function.Surjective f) [Finite f.ker]
    (r : ℤ_[q]) (g : Add.Tate.Module (H := H') q →ₗ[ℤ_[q]] Add.Tate.Module (H := H) q)
    (hgf : g.comp (Add.Tate.map q f) = r • LinearMap.id) :
    (Add.Tate.map q f).comp g = r • LinearMap.id := by
  let d := Add.Tate.map q (FiniteKernelDivision.FiniteKernel.inverseMultiple f hf)
  let m := Nat.card f.ker
  have hm : (m : ℤ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (FiniteKernelDivision.FiniteKernel.card_ne_zero f)
  have hfd : (Add.Tate.map q f).comp d = (m : ℤ_[q]) • LinearMap.id := by
    rw [Nat.cast_smul_eq_nsmul, ← Functor.Tate.map_comp, FiniteKernelDivision.FiniteKernel.comp_inverseMultiple, Functor.Tate.map_nsmul, Functor.Tate.map_id]
  apply LinearMap.ext
  intro y
  have hdy := congrArg (fun a => a y) hfd
  change Add.Tate.map q f (d y) = (m : ℤ_[q]) • y at hdy
  have hgy := congrArg (fun a => a (d y)) hgf
  change g (Add.Tate.map q f (d y)) = r • d y at hgy
  have he := congrArg (Add.Tate.map q f) hgy
  simp only [hdy, map_smul] at he
  have he' : (m : ℤ_[q]) • Add.Tate.map q f (g y) = (m : ℤ_[q]) • (r • y) :=
    he.trans (smul_comm r (m : ℤ_[q]) y)
  change Add.Tate.map q f (g y) = r • y
  apply sub_eq_zero.mp
  apply Functor.Tate.smul_eq_zero_of_ne_zero q (m : ℤ_[q]) hm
  rw [smul_sub, he', sub_self]

end ReverseSides.Tate

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N n : ℕ}
  {P Q : PEL.PELFamilyData R g N S}
  {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (q : ℕ) [Fact q.Prime]
  (e : PELIsogenies.PELIsogeny P Q n) (δ : Fin g → ℕ)
  (hδ : P.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

theorem PELIsogenies.PELIsogeny.comp_integralTateReverse :
    (Add.schemeTateMap P.abelian.scheme (Over.mk b) q e.isogeny.hom).comp
      (e.integralTateReverse b q δ hδ hq) = n • LinearMap.id := by
  let φ := (P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk b)).toAdditive
  have hf : Function.Surjective φ := FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective e.isogeny b
  have hk : Finite φ.ker := by
    have : Finite (e.isogeny.kernelAt (Over.mk b)) :=
      FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricKernel_finite e.isogeny b
    exact Finite.of_equiv (e.isogeny.kernelAt (Over.mk b)) {
      toFun x := ⟨Additive.ofMul x.val, x.property⟩
      invFun x := ⟨x.val.toMul, x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [← Nat.cast_smul_eq_nsmul ℤ_[q]]
  apply ReverseSides.Tate.reverse_comp_symm q φ hf
  rw [Nat.cast_smul_eq_nsmul]
  exact e.integralTateReverse_comp b q δ hδ hq

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
