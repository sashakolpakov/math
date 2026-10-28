import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientExact

/-! # Singular Coefficient Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientInjection

noncomputable section

/-! A cochain proof of degree-two coefficient injectivity from degree-one
lifting in a short exact coefficient sequence. -/

open _root_.CategoryTheory

variable {R : Type} [Ring R] {M N P : ModuleCat.{0} R}
  (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0})
  (hf : Function.Injective f) (hg : Function.Surjective g)
  (he : ∀ b : N, g b = 0 ↔ ∃ a : M, f a = b)
  (h1 : Function.Surjective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X 1))

include hf hg he h1

theorem singularH2_coefficient_kernel_zero (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X 2)
    (hc : AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X 2 (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M X 2 c) = 0) :
    AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M X 2 c = 0 := by
  have hfc : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass N X 2 (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap f X 2 c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass N X 2 0 := by simpa only [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, map_zero] using hc
  obtain ⟨b, hb⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ N X 1 _ _).mp hfc
  have hdb : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d 1 2 b = (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f 2 c.val := by
    exact (hb.trans (sub_zero _)).trans (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap_val (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X) 2 c)
  have hgf (a : M) : g (f a) = 0 := (he (f a)).mpr ⟨a, rfl⟩
  have hgb : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains P X).d 1 2 ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f 1 b) = 0 := by
    rw [SingularCoefficientExact.coefficientCochain_d, hdb]
    exact SingularCoefficientExact.coefficientCochain_comp_zero f g X hgf 2 c.val
  let t : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles P X 1 :=
    ⟨(AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f 1 b, (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mpr hgb⟩
  obtain ⟨a, ha⟩ := h1 (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass P X 1 t)
  obtain ⟨ac, hac⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective N X 1 a
  have ht : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass P X 1 t = AlgebraicTopology.Cohomology.Singular.Representatives.singularClass P X 1 (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap g X 1 ac) := by
    rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, hac, ha]
  obtain ⟨u, hu⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ P X 0 _ _).mp ht
  obtain ⟨v, hv⟩ := SingularCoefficientExact.coefficientCochain_surjective g X hg 0 u
  let b' := b - ac.val - (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d 0 1 v
  have hb' : (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f 1 b' = 0 := by
    dsimp only [b']
    rw [map_sub, map_sub, ← SingularCoefficientExact.coefficientCochain_d, hv, hu]
    change (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f 1 b - (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f 1 ac.val -
      ((AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f 1 b - (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f 1 ac.val) = 0
    exact sub_self _
  obtain ⟨w, hw⟩ := SingularCoefficientExact.coefficientCochain_exact f g X he 1 b' hb'
  have hacd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d 1 2 ac.val = 0 :=
    (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mp ac.property
  have hvdd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d 1 2 ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d 0 1 v) = 0 :=
    ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d_comp_d 0 1 2) v
  have hwc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d 1 2 w = c.val := by
    apply SingularCoefficientExact.coefficientCochain_injective f X hf 2
    rw [← SingularCoefficientExact.coefficientCochain_d, hw]
    dsimp only [b']
    rw [map_sub, map_sub, hacd, hvdd, sub_zero, sub_zero, hdb]
  have h := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ M X 1 c 0).mpr
    ⟨w, by simpa only [Submodule.coe_zero, sub_zero] using hwc⟩
  simpa only [map_zero] using h

theorem singularH2_coefficient_injective : Function.Injective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X 2) := by
  intro a b hab
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective M X 2 (a - b)
  have hz : AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X 2 (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M X 2 c) = 0 := by
    rw [hc, map_sub, hab, sub_self]
  have hz' := singularH2_coefficient_kernel_zero f g X hf hg he h1 c hz
  rw [hc] at hz'
  exact sub_eq_zero.mp hz'

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientInjection
