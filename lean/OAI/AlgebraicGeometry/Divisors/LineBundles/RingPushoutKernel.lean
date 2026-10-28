import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Ring Pushout Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RingPushoutKernel.BundleCycles

noncomputable section

/-! Base change of a surjective ring homomorphism carries its
actual kernel to the extended kernel ideal. -/

open _root_.CategoryTheory

theorem ringPushout_kernel {R B S T : CommRingCat.{0}} (q : R ⟶ B) (φ : R ⟶ S)
    (ψ : B ⟶ T) (q' : S ⟶ T) (hp : IsPushout q φ ψ q') (hq : Function.Surjective q) :
    RingHom.ker q'.hom = (RingHom.ker q.hom).map φ.hom := by
  let I := (RingHom.ker q.hom).map φ.hom
  let π : S ⟶ CommRingCat.of (S ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hk : ∀ r ∈ RingHom.ker q.hom, (π.hom.comp φ.hom) r = 0 := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ.hom hr)
  let u := Ideal.Quotient.lift (RingHom.ker q.hom) (π.hom.comp φ.hom) hk
  let a : B ⟶ CommRingCat.of (S ⧸ I) :=
    CommRingCat.ofHom (u.comp (q.hom.quotientKerEquivOfSurjective hq).symm.toRingHom)
  have ha : q ≫ a = φ ≫ π := by
    ext r
    change u ((q.hom.quotientKerEquivOfSurjective hq).symm (q r)) = π (φ r)
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl
  let δ := hp.desc a π ha
  have hδ : q' ≫ δ = π := hp.inr_desc a π ha
  apply le_antisymm
  · intro s hs
    change q' s = 0 at hs
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := ConcreteCategory.congr_hom hδ s
    change δ (q' s) = π s at he
    exact he.symm.trans (by rw [hs, map_zero])
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change q r = 0 at hr
    change q' (φ r) = 0
    have he := ConcreteCategory.congr_hom hp.w r
    change ψ (q r) = q' (φ r) at he
    exact he.symm.trans (by rw [hr, map_zero])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.RingPushoutKernel.BundleCycles
