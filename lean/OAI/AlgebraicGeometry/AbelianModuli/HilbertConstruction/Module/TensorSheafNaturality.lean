import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionTensorNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PushedScalarNaturality

/-! # Tensor Sheaf Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSheafNaturality

noncomputable section

/-! The tensor comparison is natural in the module sheaf, allowing it to be transported along actual trivializations. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤)) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp f)

theorem moduleSectionTensorComparisonApp_sheaf_natural {M N : X.Modules} (e : M ⟶ N)
    (U : X.Opens) (b : B) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    SectionTensorComparison.moduleSectionTensorComparisonApp a f N q hq U
      (b ⊗ₜ[R] ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map e).app (.op U) x) =
      ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map
        ((Scheme.Modules.pushforward a).map ((Scheme.Modules.pullback a).map e))).app (.op U)
          (SectionTensorComparison.moduleSectionTensorComparisonApp a f M q hq U (b ⊗ₜ[R] x)) := by
  have hleft := SectionTensorComparison.moduleSectionTensorComparisonApp_tmul a f N q hq U b
    (((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map e).app (.op U) x)
  have hright := congrArg (fun z => ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map
    ((Scheme.Modules.pushforward a).map ((Scheme.Modules.pullback a).map e))).app (.op U) z)
      (SectionTensorComparison.moduleSectionTensorComparisonApp_tmul a f M q hq U b x)
  have hα := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap_natural a f e) (.op U)) x
  have hσ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (PushedScalarNaturality.pushedCoefficientScalarRingHom_natural a f q ((Scheme.Modules.pullback a).map e) b) (.op U))
      ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f M).app (.op U) x)
  exact hleft.trans (((congrArg (fun z =>
    Section.PresheafExtendedScalars.pushedCoefficientScalarComponent a f ((Scheme.Modules.pullback a).obj N) q U b z)
      hα).trans hσ.symm).trans hright.symm)

theorem moduleSectionTensorComparison_sheaf_natural {M N : X.Modules} (e : M ⟶ N) :
    CategoryTheory.Functor.whiskerRight ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map e) (tensorLeft (ModuleCat.of R B)) ≫
        SectionTensorNaturality.moduleSectionTensorComparison a f N q hq =
      SectionTensorNaturality.moduleSectionTensorComparison a f M q hq ≫
        (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).map
          ((Scheme.Modules.pushforward a).map ((Scheme.Modules.pullback a).map e)) := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro b x
  exact moduleSectionTensorComparisonApp_sheaf_natural a f q hq e U.unop b x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorSheafNaturality
