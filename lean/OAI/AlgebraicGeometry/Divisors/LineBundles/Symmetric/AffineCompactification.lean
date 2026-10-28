import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartEquiv

/-! # Affine Compactification -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification.BundleCycles

noncomputable section

/-! The affine symmetric spectrum embeds as the distinguished open in
the actual projective spectrum of the augmented module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] Augmented.SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartAlgebra

def augmentedSymmetricAffineChartIso :
    (Proj.basicOpen (Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)).toScheme ≅
      Spec (.of (SymmetricAlgebra R M)) :=
  Proj.basicOpenIsoSpec (Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)
    (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (by decide : 0 < 1) ≪≫
      Scheme.Spec.mapIso (Augmented.SymmetricChartEquiv.BundleCycles.augmentedSymmetricChartEquiv R M).toRingEquiv.toCommRingCatIso.symm.op

def symmetricAffineCompactification :
    Spec (.of (SymmetricAlgebra R M)) ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) :=
  Spec.map (CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M)) ≫
    Proj.awayι (Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)
      (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (by decide : 0 < 1)

instance symmetricAffineCompactification_isOpenImmersion :
    IsOpenImmersion (symmetricAffineCompactification R M) := by
  let e := (Augmented.SymmetricChartEquiv.BundleCycles.augmentedSymmetricChartEquiv R M).toRingEquiv.toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M)) := e.isIso_hom
  unfold symmetricAffineCompactification
  infer_instance

theorem symmetricAffineCompactification_opensRange :
    (symmetricAffineCompactification R M).opensRange =
      Proj.basicOpen (Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) := by
  let e := (Augmented.SymmetricChartEquiv.BundleCycles.augmentedSymmetricChartEquiv R M).toRingEquiv.toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M)) := e.isIso_hom
  unfold symmetricAffineCompactification
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Proj.opensRange_awayι _ _ _ _)

theorem symmetricAffineCompactification_over :
    symmetricAffineCompactification R M ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) =
      Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M))) := by
  unfold symmetricAffineCompactification SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact Augmented.SymmetricChartScalar.BundleCycles.augmentedSymmetricDehomogenization_scalar R M r

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification.BundleCycles
