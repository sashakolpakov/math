import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalFunctionDimension

/-! # Coefficient Retraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientRetraction

noncomputable section

/-! A section of a scheme over an affine coefficient ring gives an actual coefficient-linear algebra retraction of its global regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def sectionCoefficientRetraction {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (x : Spec (.of R) ⟶ X) (hx : x ≫ p = 𝟙 _) :
    Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ⊤ →ₐ[R] R := by
  let φ : Γ(X, ⊤) →+* R := (Scheme.ΓSpecIso (.of R)).hom.hom.comp x.appTop.hom
  refine { __ := φ, commutes' := fun r => ?_ }
  have hpx : p.appTop ≫ x.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hx]
    rfl
  have H : (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫ x.appTop ≫
      (Scheme.ΓSpecIso (.of R)).hom = 𝟙 (CommRingCat.of R) := by
    rw [← Category.assoc p.appTop x.appTop, hpx, Category.id_comp, Iso.inv_hom_id]
  change φ (Coefficient.AlgebraPresheaf.coefficientSectionMap (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) ⊤ r) = r
  rw [Coefficient.GlobalFunctionDimension.coefficientSectionMap_top]
  exact ConcreteCategory.congr_hom H r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientRetraction
