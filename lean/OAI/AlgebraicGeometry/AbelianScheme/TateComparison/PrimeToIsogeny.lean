import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricIsogeny

/-! # Prime To Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PrimeToIsogeny

noncomputable section

/-! A prime-to-q kernel gives an integral Tate isomorphism. The inverse
is the actual finite-kernel inverse multiple divided by its unit cardinal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace Tate

universe u
variable (q : ℕ) [Fact q.Prime] {H H' : Type u} [AddCommGroup H] [AddCommGroup H']

def integralEquivOfUnitKernelCard (f : H →+ H') (hf : Function.Surjective f)
    (hm : IsUnit (Nat.card f.ker : ℤ_[q])) :
    Add.Tate.Module (H := H) q ≃ₗ[ℤ_[q]] Add.Tate.Module (H := H') q := by
  let g := FiniteKernelDivision.FiniteKernel.inverseMultiple f hf
  let m := Nat.card f.ker
  let u := hm.unit
  have hu : (u : ℤ_[q]) = (m : ℤ_[q]) := hm.unit_spec
  have hgf : (Add.Tate.map q g).comp (Add.Tate.map q f) = m • LinearMap.id := by
    rw [← Functor.Tate.map_comp, FiniteKernelDivision.FiniteKernel.inverseMultiple_comp, Functor.Tate.map_nsmul, Functor.Tate.map_id]
  have hfg : (Add.Tate.map q f).comp (Add.Tate.map q g) = m • LinearMap.id := by
    rw [← Functor.Tate.map_comp, FiniteKernelDivision.FiniteKernel.comp_inverseMultiple, Functor.Tate.map_nsmul, Functor.Tate.map_id]
  refine LinearEquiv.ofLinearMap (Add.Tate.map q f) ((↑u⁻¹ : ℤ_[q]) • Add.Tate.map q g) ?_ ?_
  · rw [LinearMap.comp_smul, hfg, ← Nat.cast_smul_eq_nsmul ℤ_[q], ← hu, smul_smul,
      Units.inv_mul, one_smul]
  · rw [LinearMap.smul_comp, hgf, ← Nat.cast_smul_eq_nsmul ℤ_[q], ← hu, smul_smul,
      Units.inv_mul, one_smul]

theorem integralEquivOfUnitKernelCard_toLinearMap (f : H →+ H') (hf : Function.Surjective f)
    (hm : IsUnit (Nat.card f.ker : ℤ_[q])) :
    (integralEquivOfUnitKernelCard q f hf hm).toLinearMap = Add.Tate.map q f := rfl

end Tate

universe u
variable {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)
  (q : ℕ) [Fact q.Prime]

def geometricIntegralTateIsogenyEquiv (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hm : IsUnit (Nat.card (f.kernelAt (Over.mk b)) : ℤ_[q])) :
    Add.schemeTateModule A.scheme (Over.mk b) q ≃ₗ[ℤ_[q]]
      Add.schemeTateModule B.scheme (Over.mk b) q := by
  let φ := (A.mapPoints B f.hom (Over.mk b)).toAdditive
  have he : f.kernelAt (Over.mk b) ≃ φ.ker := {
    toFun x := ⟨Additive.ofMul x.val, x.property⟩
    invFun x := ⟨x.val.toMul, x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hm' : IsUnit (Nat.card φ.ker : ℤ_[q]) := by
    rw [← Nat.card_congr he]
    exact hm
  exact Tate.integralEquivOfUnitKernelCard q φ
    (FrobeniusKernel.GeometricIsogeny.Construction.isogeny_geometricPoints_surjective f b) hm'

theorem geometricIntegralTateIsogenyEquiv_toLinearMap (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (hm : IsUnit (Nat.card (f.kernelAt (Over.mk b)) : ℤ_[q])) :
    (geometricIntegralTateIsogenyEquiv b q f hm).toLinearMap =
      Add.schemeTateMap A.scheme (Over.mk b) q f.hom := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PrimeToIsogeny
