import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleTensorTarget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorNaturality

/-! # Module Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleTensorComparison

noncomputable section

/-! For the structure module, the actual section tensor comparison is the ordinary multiplication-of-functions tensor comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem structureModuleTensorComparison_tmul
    {X Y : Scheme.{u}} {R : Type u} [CommRing R]
    (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (B : CommAlgCat.{u} R) (q : B →+* Γ(Y, ⊤))
    (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f) (U : X.Opens) (b : B)
    (r : (Coefficient.ModulePresheaf.coefficientModulePresheaf f (Line.Bundles.structureModule X)).obj (.op U)) :
    (ModuleTensorTarget.baseChangedStructureModuleSectionsIso a f).hom.app (.op U)
      (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a f (Line.Bundles.structureModule X) q hq U (b ⊗ₜ[R] r)) =
        (Tensor.SectionModules.tensorSectionModuleComparison a f B q hq).app (.op U)
          (b ⊗ₜ[R] Coefficient.StructureModuleComparison.coefficientStructureModuleComponent f U r) := by
  let V := a ⁻¹ᵁ U
  let u : Γ((Scheme.Modules.pullback a).obj (Line.Bundles.structureModule X), V) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app (Line.Bundles.structureModule X)).app U r
  have hu : (Line.Bundles.structureModulePullbackIso a).hom.app V u = a.app U r :=
    ModuleTensorTarget.baseChangedStructureModuleSectionsIso_unit a f U r
  change (Line.Bundles.structureModulePullbackIso a).hom.app V
    (Y.presheaf.map V.leTop.op (q b) • u) = Y.presheaf.map V.leTop.op (q b) * a.app U r
  exact ((Line.Bundles.structureModulePullbackIso a).hom.app_smul (Y.presheaf.map V.leTop.op (q b)) u).trans
    (congrArg (fun z : Γ(Y, V) => Y.presheaf.map V.leTop.op (q b) * z) hu)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleTensorComparison
