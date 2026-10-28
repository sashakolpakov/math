import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorComparison
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-! # Section Tensor Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorNaturality

noncomputable section

/-! The actual module-section tensor comparisons commute with restriction and therefore form a morphism of coefficient-module presheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)

theorem moduleSectionTensorComparisonApp_natural {U V : X.Opens} (h : V ≤ U) (b : B)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq V
      (b ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).map (homOfLE h).op x) =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M))).map
        (homOfLE h).op (SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U (b ⊗ₜ[R] x)) := by
  rw [SectionTensorComparison.moduleSectionTensorComparisonApp_tmul, SectionTensorComparison.moduleSectionTensorComparisonApp_tmul]
  let α := Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f M
  let σ := Section.PresheafExtendedScalars.pushedCoefficientScalarRingHom a f ((Scheme.Modules.pullback a).obj M) q b
  have hα := ConcreteCategory.congr_hom (α.naturality (homOfLE h).op) x
  have hσ := ConcreteCategory.congr_hom (σ.naturality (homOfLE h).op) (α.app (.op U) x)
  exact (congrArg (fun z => σ.app (.op V) z) hα).trans hσ

def moduleSectionTensorComparison :
    Coefficient.ModulePresheaf.coefficientModulePresheaf f M ⋙ tensorLeft (ModuleCat.of R B) ⟶
      Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) where
  app U := ModuleCat.ofHom
    (X := (Coefficient.ModulePresheaf.coefficientModulePresheaf f M ⋙ tensorLeft (ModuleCat.of R B)).obj U)
    (Y := (Coefficient.ModulePresheaf.coefficientModulePresheaf f
      ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M))).obj U)
    (SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U.unop)
  naturality U V h := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro b x
    exact moduleSectionTensorComparisonApp_natural a f M q hq h.unop.le b x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorNaturality
