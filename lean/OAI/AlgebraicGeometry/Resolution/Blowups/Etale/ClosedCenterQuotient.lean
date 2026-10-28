import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PointedSmoothCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedCarrierCenters

/-! # Closed Center Quotient -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedCenterQuotient.Construction

noncomputable section

/-! Smooth native centers remain smooth in actual étale affine quotient charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem idealSheaf_complex_center_quotient_on_etale_chart
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData) [Smooth (I.subschemeι ≫ f)]
    (R : CommRingCat) [Algebra ℂ R] (j : Spec R ⟶ X) [Etale j]
    (hj : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (K : Ideal R)
    (hK : I.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel K) : Algebra.Smooth ℂ (R ⧸ K) := by
  let l := (I.comapIso j).hom ≫ pullback.snd j I.subschemeι
  have hl : l ≫ I.subschemeι = (I.comap j).subschemeι ≫ j := by
    dsimp only [l]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  let : Etale l := by dsimp only [l]; infer_instance
  have hs : Smooth (l ≫ (I.subschemeι ≫ f)) := inferInstance
  rw [← Category.assoc, hl, Category.assoc, hK, hj] at hs
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))
  let : Smooth (i.imageι ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := hs
  have hi : Smooth (i ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) := by
    rw [← i.toImage_imageι, Category.assoc]
    infer_instance
  have he : i ≫ ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (R ⧸ K) := by
    rw [ComplexAffineDifferentialIdeal.Construction.complexSpecStructure, ← Spec.map_comp]
    rfl
  rw [he] at hi
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
    (φ := CommRingCat.ofHom (algebraMap ℂ (R ⧸ K)))).mp hi)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedCenterQuotient.Construction
