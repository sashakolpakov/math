import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationAdditiveUnit
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

/-! # Analytification Cech Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechMap

noncomputable section

/-! The original module analytification unit induces its normalized map of native Čech complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (M : SheafOfModules.{0} X.left.ringCatSheaf) {ι : Type} (U : ι → X.left.Opens)

def moduleAnalytificationCechMap :
    (cechComplexFunctor U).obj M.val.presheaf ⟶
      (cechComplexFunctor (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))).obj
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf :=
  (cechComplexFunctor U).map (AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M) ≫
    (AdditiveCechImage.additiveCechDirectImageIso (Analytification.Base.analytificationMap X) U
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf).hom

theorem moduleAnalytificationCechMap_proj (q : ℕ) (t : Fin (q + 1) → ι) :
    (moduleAnalytificationCechMap X M U).f q ≫
        Pi.π (fun a : Fin (q + 1) → ι =>
          ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf.obj
            (op (∏ᶜ fun k => Open.AffineIsoEvaluation.analyticOpen X (U (a k))))) t =
      Pi.π (fun a : Fin (q + 1) → ι => M.val.presheaf.obj (op (∏ᶜ fun k => U (a k)))) t ≫
        (AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M).app (op (∏ᶜ fun k => U (t k))) ≫
          (AdditiveCechImage.additiveCechDirectImageSectionIso (Analytification.Base.analytificationMap X) U
            ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf q t).hom := by
  let α := AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M
  let φ := ((cechComplexFunctor U).map α).f q
  let e := (AdditiveCechImage.additiveCechDirectImageTermIso (Analytification.Base.analytificationMap X) U
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf q).hom
  let b := (AdditiveCechImage.additiveCechDirectImageSectionIso (Analytification.Base.analytificationMap X) U
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf q t).hom
  let p := Pi.π (fun a : Fin (q + 1) → ι =>
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf.obj
      (op ((Opens.map (Analytification.Base.analytificationMap X)).obj (∏ᶜ fun k => U (a k))))) t
  let r := Pi.π (fun a : Fin (q + 1) → ι =>
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf.obj
      (op (∏ᶜ fun k => Open.AffineIsoEvaluation.analyticOpen X (U (a k))))) t
  let p₀ := Pi.π (fun a : Fin (q + 1) → ι => M.val.presheaf.obj (op (∏ᶜ fun k => U (a k)))) t
  have he : e ≫ r = p ≫ b := AdditiveCechImage.additiveCechDirectImageTermIso_hom_proj (Analytification.Base.analytificationMap X) U
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf q t
  have hφ : φ ≫ p = p₀ ≫ α.app (op (∏ᶜ fun k => U (t k))) :=
    Pi.map_π (fun a : Fin (q + 1) → ι => α.app (op (∏ᶜ fun k => U (a k)))) t
  exact (Category.assoc φ e r).trans ((congrArg (φ ≫ ·) he).trans
    ((Category.assoc φ p b).symm.trans ((congrArg (· ≫ b) hφ).trans (Category.assoc _ _ _))))

theorem moduleAnalytificationCechMap_coordinate (q : ℕ)
    (z : ((cechComplexFunctor U).obj M.val.presheaf).X q) (t : Fin (q + 1) → ι) :
    SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf
        (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i)) q ((moduleAnalytificationCechMap X M U).f q z) t =
      (AdditiveCechImage.additiveCechDirectImageSectionIso (Analytification.Base.analytificationMap X) U
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf q t).hom
        ((AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M).app (op (∏ᶜ fun k => U (t k)))
          (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv M.val.presheaf U q z t)) := by
  have h := ConcreteCategory.congr_hom (moduleAnalytificationCechMap_proj X M U q t) z
  exact (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply _ _ q _ t).trans
    (h.trans (congrArg (fun a => (AdditiveCechImage.additiveCechDirectImageSectionIso (Analytification.Base.analytificationMap X) U
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf q t).hom
        ((AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M).app (op (∏ᶜ fun k => U (t k))) a))
          (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv_apply M.val.presheaf U q z t).symm))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechMap
