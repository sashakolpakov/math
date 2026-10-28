import OAI.CategoryTheory.Isomorphisms.TransportedIsoSquare
import OAI.AlgebraicTopology.Cohomology.ModuleCarrier
import OAI.Algebra.Modules.ScalarModuleUnderlyingGroup
import OAI.AlgebraicGeometry.Sheaves.ModuleSheafRestrictionCarrier
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalCohomologyExcision
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor

/-! # Cohomology Excision -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CohomologyExcision

noncomputable section

/-! Two-open excision for module sheaves is linear over every coefficient ring
acting through the actual global functions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false

private def linearIsoOfScalarSquare {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R)
    (e : (forget₂ (ModuleCat R) AddCommGrpCat).obj M ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj N)
    (h : ∀ r : R, M.smul r ≫ e.hom =
      e.hom ≫ N.smul r) : M ≅ N := by
  let l : M ≃ₗ[R] N := { e.addCommGroupIsoToAddEquiv with
    map_smul' := fun r x => ConcreteCategory.congr_hom (h r) x }
  exact l.toModuleIso

private def forgottenCoefficientExcisionIso
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (M : X.Modules) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hV : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict V.ι) q))
    (hUV : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict (U ⊓ V).ι) q)) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M) ≅
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (U.ι.appTop.hom.comp c) n).obj
        (M.restrict U.ι)) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let e := NaturalCohomologyExcision.IntrinsicCech.naturalSheafCohomologyTwoOpenExcisionIso F U V hcover (fun q => AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.moduleOpenCohomologySubsingleton M V q (hV q)) (fun q => AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.moduleOpenCohomologySubsingleton M (U ⊓ V) q (hUV q)) n
  exact eqToIso (AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.coefficientCohomologyUnderlying c M n) ≪≫ e ≪≫
    (eqToIso (AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.coefficientOpenCohomologyUnderlying c M U n)).symm

private theorem coefficientExcisionScalarSquare
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (M : X.Modules) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hV : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict V.ι) q))
    (hUV : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict (U ⊓ V).ι) q)) (n : ℕ) (r : R) :
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M).smul r ≫
        (forgottenCoefficientExcisionIso c M U V hcover hV hUV n).hom =
      (forgottenCoefficientExcisionIso c M U V hcover hV hUV n).hom ≫
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (U.ι.appTop.hom.comp c) n).obj
          (M.restrict U.ι)).smul r := by
  let a := Global.ModuleScalars.globalModuleScalar M (c r)
  let t := (SheafOfModules.toSheaf X.ringCatSheaf).map a
  have hs : (TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).map t =
      (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
        (Global.ModuleScalars.globalModuleScalar (M.restrict U.ι) (U.ι.appTop (c r))) := by
    change (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
      ((Scheme.Modules.restrictFunctor U.ι).map (Global.ModuleScalars.globalModuleScalar M (c r))) = _
    rw [Global.ScalarRestriction.globalModuleScalar_restrict]
  have h := NaturalCohomologyExcision.IntrinsicCech.naturalSheafCohomologyTwoOpenExcisionIso_naturality
    t U V hcover (fun q => AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.moduleOpenCohomologySubsingleton M V q (hV q)) (fun q => AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.moduleOpenCohomologySubsingleton M (U ⊓ V) q (hUV q)) (fun q => AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.moduleOpenCohomologySubsingleton M V q (hV q)) (fun q => AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.moduleOpenCohomologySubsingleton M (U ⊓ V) q (hUV q)) n
  rw [hs] at h
  exact CategoryTheory.Isomorphisms.TransportedIsoSquare.transportedIsoSquare
    (AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.coefficientCohomologyUnderlying c M n) (AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.coefficientOpenCohomologyUnderlying c M U n)
    (NaturalCohomologyExcision.IntrinsicCech.naturalSheafCohomologyTwoOpenExcisionIso
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U V hcover (fun q => AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.moduleOpenCohomologySubsingleton M V q (hV q)) (fun q => AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.moduleOpenCohomologySubsingleton M (U ⊓ V) q (hUV q)) n)
    (AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.additiveSheafCohomologyMap t n) _
    (AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.additiveSheafCohomologyMap
      ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
        (Global.ModuleScalars.globalModuleScalar (M.restrict U.ι) (U.ι.appTop (c r)))) n) _
    (AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.coefficientCohomologyUnderlying_smul c M n r)
    (AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction.coefficientOpenCohomologyUnderlying_smul c M U n r) h

def coefficientCohomologyTwoOpenExcisionIso
    {X : Scheme.{u}} {R : Type u} [CommRing R] (c : R →+* Γ(X, ⊤))
    (M : X.Modules) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (hV : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict V.ι) q))
    (hUV : ∀ q, Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict (U ⊓ V).ι) q)) (n : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (U.ι.appTop.hom.comp c) n).obj
        (M.restrict U.ι) := by
  exact linearIsoOfScalarSquare _ _
    (forgottenCoefficientExcisionIso c M U V hcover hV hUV n)
    (coefficientExcisionScalarSquare c M U V hcover hV hUV n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CohomologyExcision
