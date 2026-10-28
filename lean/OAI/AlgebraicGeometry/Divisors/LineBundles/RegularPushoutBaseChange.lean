import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularTensorBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularRingEquiv
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.RingHom.Flat

/-! # Regular Pushout Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RegularPushoutBaseChange.BundleCycles

noncomputable section

/-! Regular equations with a flat cokernel stay regular in
an actual pushout of coefficient rings. -/

open _root_.CategoryTheory TensorProduct

theorem regular_pushout_baseChange
    {R A B C T : CommRingCat.{0}} (a : R ⟶ A) (b : R ⟶ B)
    (i : A ⟶ T) (j : B ⟶ T) (hp : IsPushout a b i j)
    (q : A ⟶ C) (hq : Function.Surjective q)
    (hc : (a ≫ q).hom.Flat) (t : A) (ht : IsRegular t)
    (hk : RingHom.ker q.hom = Ideal.span {t}) : IsRegular (i t) := by
  algebraize [a.hom, b.hom, (a ≫ q).hom]
  let : Module.Flat R C := hc
  let ql : A →ₗ[R] C := {
    toFun := q
    map_add' := q.hom.map_add
    map_smul' := fun r x => q.hom.map_mul (a r) x
  }
  have hker (x : A) : ql x = 0 ↔ x ∈ Ideal.span {t} := by
    rw [← hk]
    rfl
  have hreg := RegularTensorBaseChange.BundleCycles.regular_tensor_baseChange_of_flat_cokernel R A B t ht ql hq hker
  let H := CommRingCat.isPushout_tensorProduct R B A
  let e : CommRingCat.of (B ⊗[R] A) ≅ T := H.isoIsPushout B A hp.flip
  have he : e.hom (1 ⊗ₜ[R] t) = i t :=
    ConcreteCategory.congr_hom (H.inr_isoIsPushout_hom B A hp.flip) t
  exact he ▸ RegularRingEquiv.BundleCycles.regular_ringEquiv e.commRingCatIsoToRingEquiv (1 ⊗ₜ[R] t) hreg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.RegularPushoutBaseChange.BundleCycles
