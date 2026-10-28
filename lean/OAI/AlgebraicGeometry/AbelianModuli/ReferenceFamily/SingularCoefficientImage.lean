import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientExact

/-! # Singular Coefficient Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientImage

noncomputable section

/-! Exactness at the middle term of singular cohomology for a short
exact coefficient sequence. The lift is constructed from actual cochains. -/

open _root_.CategoryTheory

variable {R : Type} [Ring R] {M N P : ModuleCat.{0} R}
  (f : M ⟶ N) (g : N ⟶ P) (X : TopCat.{0})
  (hf : Function.Injective f) (hg : Function.Surjective g)
  (he : ∀ b : N, g b = 0 ↔ ∃ a : M, f a = b)

include hf hg he in
theorem singularCoefficient_lift_of_zero (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology N X (n + 1))
    (ha : AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X (n + 1) a = 0) :
    ∃ b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X (n + 1),
      AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X (n + 1) b = a := by
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective N X (n + 1) a
  have hgc : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass P X (n + 1) (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap g X (n + 1) c) =
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass P X (n + 1) 0 := by
    rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, hc, ha, map_zero]
  obtain ⟨u, hu⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ P X n _ _).mp hgc
  have hdu : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains P X).d n (n + 1) u =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f (n + 1) c.val := by
    exact (hu.trans (sub_zero _)).trans
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap_val (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X) (n + 1) c)
  obtain ⟨v, hv⟩ := SingularCoefficientExact.coefficientCochain_surjective g X hg n u
  let c' := c.val - (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d n (n + 1) v
  have hgc' : (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap g X).f (n + 1) c' = 0 := by
    dsimp only [c']
    rw [map_sub, ← SingularCoefficientExact.coefficientCochain_d, hv, hdu, sub_self]
  obtain ⟨w, hw⟩ := SingularCoefficientExact.coefficientCochain_exact f g X he (n + 1) c' hgc'
  have hdc : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d (n + 1) (n + 2) c.val = 0 :=
    (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mp c.property
  have hdd : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d (n + 1) (n + 2)
      ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d n (n + 1) v) = 0 :=
    ConcreteCategory.congr_hom ((AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d_comp_d n (n + 1) (n + 2)) v
  have hdw : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).d (n + 1) (n + 2) w = 0 := by
    apply SingularCoefficientExact.coefficientCochain_injective f X hf (n + 2)
    rw [map_zero, ← SingularCoefficientExact.coefficientCochain_d, hw]
    dsimp only [c']
    rw [map_sub, hdc, hdd, sub_self]
  let b : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles M X (n + 1) :=
    ⟨w, (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ _ _).mpr hdw⟩
  refine ⟨AlgebraicTopology.Cohomology.Singular.Representatives.singularClass M X (n + 1) b, ?_⟩
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class]
  have hb : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass N X (n + 1) c =
      AlgebraicTopology.Cohomology.Singular.Representatives.singularClass N X (n + 1) (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap f X (n + 1) b) := by
    apply (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ N X n _ _).mpr
    refine ⟨v, ?_⟩
    change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains N X).d n (n + 1) v =
      c.val - (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap f X).f (n + 1) w
    rw [hw]
    dsimp only [c']
    abel
  exact hb.symm.trans hc

include he in
theorem singularCoefficient_comp_zero (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X n (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X n a) = 0 := by
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective M X n a
  rw [← hc, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientMap_class]
  have hz : AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap g X n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.coefficientCocycleMap f X n c) = 0 := by
    apply Subtype.ext
    exact SingularCoefficientExact.coefficientCochain_comp_zero f g X
      (fun x => (he (f x)).mpr ⟨x, rfl⟩) n c.val
  rw [hz, map_zero]

include hf hg he in
theorem singularCoefficient_image_iff (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology N X (n + 1)) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap g X (n + 1) a = 0 ↔
      ∃ b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X (n + 1),
        AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap f X (n + 1) b = a := by
  constructor
  · exact singularCoefficient_lift_of_zero f g X hf hg he n a
  · rintro ⟨b, rfl⟩
    exact singularCoefficient_comp_zero f g X he (n + 1) b

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientImage
