import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.OrdinaryAffineVanishing
import OAI.AlgebraicGeometry.Crystalline.Cohomology.RestrictedCoefficient
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSheaf

/-! # Affine Open Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineOpenResolution.FlatBaseAffineOpenResolution

noncomputable section

/-! # Actual injective-resolution sections of ordinary forms are exact on affine opens -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R]

def openModel (Y : Over (Spec (CommRingCat.of R))) (W : Y.left.Opens) :
    Over (Spec (CommRingCat.of R)) := Over.mk (W.ι ≫ Y.hom)

def inclusion (Y : Over (Spec (CommRingCat.of R))) (W : Y.left.Opens) :
    openModel R Y W ⟶ Y := Over.homMk W.ι

variable [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of R))) (g : Y ⟶ X) [IsOpenImmersion g.left]

local instance coefficientExt (Z : Over (Spec (CommRingCat.of R))) :
    HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves R Z) := HasExt.standard _

include g in
theorem forms_exactAt (j : ℕ) (I : InjectiveResolution ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j))
    (W : Y.left.Opens) (hW : IsAffineOpen W) (n : ℕ) :
    (((OpenSheaf.OpenSheafSectionComplex.sections R Y.left W).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).ExactAt (n + 1) := by
  let Z := openModel R Y W
  let h : Z ⟶ Y := inclusion R Y W
  let : IsAffine Z.left := hW
  let : IsOpenImmersion h.left := inferInstanceAs (IsOpenImmersion W.ι)
  let : IsOpenImmersion (h ≫ g).left := inferInstanceAs (IsOpenImmersion (W.ι ≫ g.left))
  let : Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Z)
      ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Z).X j) (n + 1)) :=
    OrdinaryAffineVanishing.FlatBaseOrdinaryAffineVanishing.forms R X Z (h ≫ g) j n
  let e : Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Z)
      ((Cech.Cover.CechRestriction.sheafRestrictionFunctor R h.left).obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j))
        (n + 1) ≃ₗ[R]
      Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Z) ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Z).X j) (n + 1) :=
    SheafCohomology.Ext.Projective.extRightIso R (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Z)
      (NumberTheory.PadicHodge.GeometricComparison.OpenForms.OpenFormsSheaves.sheafIso h j) (n + 1)
  let : Subsingleton (Ext.{u + 1} (ConstantSheaf.ConstantSheafSections.coefficient R (TopCat.of Z.left))
      ((Cech.Cover.CechRestriction.sheafRestrictionFunctor R h.left).obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j))
        (n + 1)) := e.injective.subsingleton
  have he : W.ι ''ᵁ ⊤ = W := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  exact (RestrictedCoefficient.RestrictedCoefficientResolution.exactAt R h.left I n).of_iso
    (OpenSheaf.OpenSheafSectionComplex.complexIso R W.ι W he I.cocomplex)

include g in
theorem forms_sections_exact (j : ℕ)
    (I : InjectiveResolution ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j))
    (W : Y.left.Opens) (hW : IsAffineOpen W) (n : ℕ)
    (x : (I.cocomplex.X (n + 1)).obj.obj (op W))
    (hx : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op W) x = 0) :
    ∃ y : (I.cocomplex.X n).obj.obj (op W),
      (I.cocomplex.d n (n + 1)).hom.app (op W) y = x := by
  have h := forms_exactAt R X Y g j I W hW n
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at h
  exact (ShortComplex.moduleCat_exact_iff _).mp h x hx

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineOpenResolution.FlatBaseAffineOpenResolution
