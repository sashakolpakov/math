import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSectionModules

/-! # Chart Coefficient Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartCoefficientSections

noncomputable section

/-! An affine chart over a coefficient ring identifies its regular functions with the chart algebra, preserving the coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] {X : Scheme.{u}}

def schemeGlobalCoefficient (p : X ⟶ Spec (.of R)) : R →+* Γ(X, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

def affineChartSectionsIso (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme) :
    Γ(X, U) ≅ CommRingCat.of A :=
  U.topIso.symm ≪≫ Scheme.Γ.mapIso e.op ≪≫ Scheme.ΓSpecIso (.of A)

theorem affineChartSectionsIso_coefficients (p : X ⟶ Spec (.of R))
    (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme) (φ : R →+* A)
    (h : e.hom ≫ U.ι ≫ p = Spec.map (CommRingCat.ofHom φ)) :
    CommRingCat.ofHom (Coefficient.AlgebraPresheaf.coefficientSectionMap (schemeGlobalCoefficient p) U) ≫
      (affineChartSectionsIso U e).hom = CommRingCat.ofHom φ := by
  change (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
    U.topIso.inv ≫ e.hom.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom = _
  rw [← Open.FunctionsBaseChange.openInclusion_appTop_topIso]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = (Scheme.ΓSpecIso (.of R)).inv ≫ (e.hom ≫ U.ι ≫ p).appTop ≫
        (Scheme.ΓSpecIso (.of A)).hom := by simp only [Scheme.Hom.comp_appTop, Category.assoc]
    _ = (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop ≫
        (Scheme.ΓSpecIso (.of A)).hom := by rw [h]
    _ = CommRingCat.ofHom φ := by
      rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ),
        Category.assoc, Iso.inv_hom_id, Category.comp_id]

def affineChartCoefficientAlgEquiv [Algebra R A] (p : X ⟶ Spec (.of R))
    (U : X.Opens) (e : Spec (.of A) ≅ U.toScheme)
    (h : e.hom ≫ U.ι ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Coefficient.AlgebraPresheaf.coefficientAlgebraSections (schemeGlobalCoefficient p) U ≃ₐ[R] A where
  __ := (affineChartSectionsIso U e).commRingCatIsoToRingEquiv
  commutes' r := ConcreteCategory.congr_hom (affineChartSectionsIso_coefficients p U e (algebraMap R A) h) r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartCoefficientSections
