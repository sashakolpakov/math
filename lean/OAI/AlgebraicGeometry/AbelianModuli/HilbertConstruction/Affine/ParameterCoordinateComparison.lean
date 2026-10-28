import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecGlobalSectionIdentities

/-! # Parameter Coordinate Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterCoordinateComparison

noncomputable section

/-! An affine parameter scheme can be replaced by the spectrum of its actual
global functions without changing the Cartesian square or coefficient maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem affineCoordinateMap_of_appTop {Y T : Scheme.{u}} [IsAffine Y] [IsAffine T] (s : Y ⟶ T) :
    QuotientCoefficientMap.affineCoordinateMap s.appTop.hom = Y.isoSpec.inv ≫ s :=
  Scheme.isoSpec_inv_naturality s

theorem specBaseCoefficientMap_isoSpec_inv_comp
    {Y T : Scheme.{u}} [IsAffine Y] [IsAffine T] (s : Y ⟶ T) :
    Spec.CoefficientCechComparison.specBaseCoefficientMap (Y.isoSpec.inv ≫ s) = s.appTop.hom := by
  rw [← affineCoordinateMap_of_appTop, QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap]

theorem specPullbackCoefficientMap_comp_isoSpec_hom
    {Q Y : Scheme.{u}} [IsAffine Y] (b : Q ⟶ Y) :
    Spec.CoefficientCechComparison.specPullbackCoefficientMap (b := b ≫ Y.isoSpec.hom) = b.appTop.hom := by
  ext r
  change b.appTop (Coefficient.ModulePresheaf.schemeCoefficientMap Y.toSpecΓ r) = b.appTop r
  rw [SpecGlobalSectionIdentities.schemeCoefficientMap_toSpecΓ]
  rfl

theorem affineParameter_isPullback_spec
    {Q P Y T : Scheme.{u}} [IsAffine Y]
    {a : Q ⟶ P} {b : Q ⟶ Y} {f : P ⟶ T} {s : Y ⟶ T}
    (H : IsPullback a b f s) :
    IsPullback a (b ≫ Y.isoSpec.hom) f (Y.isoSpec.inv ≫ s) := by
  exact H.of_iso (Iso.refl Q) (Iso.refl P) Y.isoSpec (Iso.refl T)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ParameterCoordinateComparison
