import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.AffineCoherentExt
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormFiniteness
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenForms
import OAI.AlgebraicGeometry.SheafCohomology.Ext

/-! # Ordinary Affine Vanishing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.OrdinaryAffineVanishing.FlatBaseOrdinaryAffineVanishing

noncomputable section

/-! # Original ordinary-form coefficient Ext vanishes on affine opens of smooth proper models -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of R))) (g : Y ⟶ X) [IsOpenImmersion g.left]

include g in
omit [Module.Flat ℤ R] in
theorem quasicoherent (j : ℕ) : (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf R Y j).IsQuasicoherent := by
  let : (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf R X j).IsQuasicoherent :=
    Base.ProperOrdinaryFormFiniteness.BaseSmoothProperOrdinaryFormFiniteness.quasicoherent R X j
  exact (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).prop_of_iso
    (OrdinaryFormOpen.OrdinaryFormOpenRestriction.iso R Y X g.left g.w j).symm inferInstance

variable [IsAffine Y.left]

local instance coefficientExt : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) := HasExt.standard _

include g in
theorem forms (j n : ℕ) : Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
    ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j) (n + 1)) := by
  let M := OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf R Y j
  let : M.IsQuasicoherent := quasicoherent R X Y g j
  let : Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
      (ProperCoherentExt.FlatBaseProperCoherentExt.sheaf R Y M) (n + 1)) :=
    AffineCoherentExt.FlatBaseAffineCoherentExt.subsingleton R Y M n
  exact (SheafCohomology.Ext.Projective.extRightIso R (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
    (OrdinaryFormSheaf.OrdinaryFormSheafComparison.iso R Y j) (n + 1)).symm.injective.subsingleton

theorem restriction (j n : ℕ) : Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
    ((Cech.Cover.CechRestriction.sheafRestrictionFunctor R g.left).obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j))
      (n + 1)) := by
  let : Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
      ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j) (n + 1)) := forms R X Y g j n
  let e : Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
      ((Cech.Cover.CechRestriction.sheafRestrictionFunctor R g.left).obj ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X j))
      (n + 1) ≃ₗ[R]
      Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y) ((DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y).X j) (n + 1) :=
    SheafCohomology.Ext.Projective.extRightIso R (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R Y)
      (NumberTheory.PadicHodge.GeometricComparison.OpenForms.OpenFormsSheaves.sheafIso g j) (n + 1)
  exact e.injective.subsingleton

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.OrdinaryAffineVanishing.FlatBaseOrdinaryAffineVanishing
