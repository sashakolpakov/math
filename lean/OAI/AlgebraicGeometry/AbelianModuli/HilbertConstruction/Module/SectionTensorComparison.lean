import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.PresheafExtendedScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleScalarTensorMap

/-! # Section Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorComparison

noncomputable section

/-! The scalar-extension comparison for actual module sections is specified on each open by multiplying pulled-back sections by changed-base functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)

def moduleSectionTensorComparisonApp (U : X.Opens) :
    TensorProduct R B ((Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) →ₗ[R]
      (Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M))).obj (.op U) :=
  CompatibleScalarTensorMap.compatibleScalarTensorMap
    (Section.PresheafExtendedScalars.pushedCoefficientScalarComponent a f ((Scheme.Modules.pullback a).obj M) q U)
    (Section.PresheafExtendedScalars.pushedCoefficientScalarComponent_coefficient a f ((Scheme.Modules.pullback a).obj M) q hq U)
    ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f M).app (.op U)).hom

theorem moduleSectionTensorComparisonApp_tmul (U : X.Opens) (b : B)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    moduleSectionTensorComparisonApp a f M q hq U (b ⊗ₜ[R] x) =
      Section.PresheafExtendedScalars.pushedCoefficientScalarComponent a f ((Scheme.Modules.pullback a).obj M) q U b
        ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f M).app (.op U) x) := rfl

theorem moduleSectionTensorComparisonApp_one (U : X.Opens)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    moduleSectionTensorComparisonApp a f M q hq U (1 ⊗ₜ[R] x) =
      (Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f M).app (.op U) x := by
  rw [moduleSectionTensorComparisonApp_tmul, map_one]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorComparison
