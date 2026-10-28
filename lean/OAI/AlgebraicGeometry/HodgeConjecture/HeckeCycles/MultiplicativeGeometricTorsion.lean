import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection
import Mathlib.Algebra.CharP.Reduced

/-! # Multiplicative Geometric Torsion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MultiplicativeGeometricTorsion.CM

noncomputable section

/-! In characteristic q the multiplicative group has no nontrivial
q-power torsion geometric points. The proof uses actual Laurent values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.UnitValueDetection.Construction.Schemes

universe u
variable {k : Type u} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]

theorem unit_eq_one (n : ℕ) (x : kˣ) (hx : x ^ (q ^ n) = 1) : x = 1 := by
  apply Units.ext
  have h : (x : k) ^ (q ^ n) = 1 := congrArg Units.val hx
  have h' : (x : k) ^ (q ^ n * 1) = 1 := by simpa only [mul_one] using h
  have h'' := (ExpChar.pow_prime_pow_mul_eq_one_iff q n 1 (x : k)).mp h'
  simpa only [pow_one, Units.val_one] using h''

theorem point_eq_one (n : ℕ)
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X)
    (hx : x ^ (q ^ n) = 1) : x = 1 := by
  let u := AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom (Over.mk (𝟙 (Spec (.of k))))
  let e := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  let v : Γ(Spec (.of k), ⊤)ˣ →* kˣ := Units.map e.toMonoidHom
  have hu : u x ^ (q ^ n) = 1 :=
    (map_pow u x (q ^ n)).symm.trans ((congrArg u hx).trans (map_one u))
  have hv : v (u x) ^ (q ^ n) = 1 :=
    (map_pow v (u x) (q ^ n)).symm.trans ((congrArg v hu).trans (map_one v))
  apply AbelianScheme.CartierDuality.UnitValueDetection.Construction.Schemes.multiplicativeGroupUnitHom_injective (Over.mk (𝟙 (Spec (.of k))))
  change u x = u 1
  rw [map_one]
  exact (Units.map_injective e.injective)
    ((unit_eq_one q n (v (u x)) hv).trans (map_one v).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MultiplicativeGeometricTorsion.CM
