import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PresheafUnit

/-! # Global Section Normalization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionNormalization.IntrinsicCechGlobalSectionNormalization

noncomputable section

/-! The native Čech global-section isomorphism is the actual sheafification-unit inverse followed by the original presheaf global-section comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} (U : ι → X.left.Opens) (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)

theorem presheaf_hom : (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.presheafIso R X U).hom.app F =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X U F.obj).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem unit_hom : (SectionUnit.IntrinsicCechSectionUnit.iso R X.left U).hom.app F =
    (((evaluation X.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).map
      (PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left U F).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem hom : (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R X U).hom.app F =
    ((((evaluation X.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).mapIso
      (PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left U F)).inv ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X U F.obj).hom := by
  let e := (((evaluation X.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)).mapIso
    (PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left U F)
  have he : (SectionUnit.IntrinsicCechSectionUnit.iso R X.left U).app F = e := Iso.ext (unit_hom R X U F)
  have hi : (SectionUnit.IntrinsicCechSectionUnit.iso R X.left U).inv.app F = e.inv := congrArg Iso.inv he
  exact (congrArg (fun k => k ≫ (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.presheafIso R X U).hom.app F) hi).trans
    (congrArg (fun k => e.inv ≫ k) (presheaf_hom R X U F))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionNormalization.IntrinsicCechGlobalSectionNormalization
