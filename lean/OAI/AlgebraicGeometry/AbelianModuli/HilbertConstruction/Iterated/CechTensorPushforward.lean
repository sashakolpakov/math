import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.SectionTensorValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorModelCriterion
import Mathlib.Algebra.Algebra.Bilinear

/-! # Cech Tensor Pushforward -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.CechTensorPushforward

noncomputable section

/-! Successive section tensor comparisons are compared on the original cover. The second pairing uses the actual pullback unit and pullback-composition isomorphism. Its composition with the first pairing is the direct comparison, with coefficient multiplication retained explicitly. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {X Y Z : Scheme.{u}} {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
variable [Algebra R B] [Algebra R C]
variable (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules)
variable (q : B →+* Γ(Y, ⊤)) (r : C →+* Γ(X, ⊤))
variable (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f)
variable (hr : r.comp (algebraMap R C) = (a ≫ g).appTop.hom.comp f)

def sectionTensorCoefficientProduct (α : B →ₐ[R] C) : C ⊗[R] B →ₗ[R] C :=
  TensorProduct.lift ((LinearMap.mul R C).compl₂ α.toLinearMap)

theorem sectionTensorCoefficientProduct_tmul (α : B →ₐ[R] C) (c : C) (b : B) :
    sectionTensorCoefficientProduct α (c ⊗ₜ[R] b) = c * α b := rfl

def refinementSectionTensorComparisonApp (U : Z.Opens) :
    C ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf f
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))).obj (op U)) →ₗ[R]
      (Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward (a ≫ g)).obj
        ((Scheme.Modules.pullback (a ≫ g)).obj M))).obj (op U) :=
  CompatibleScalarTensorMap.compatibleScalarTensorMap
    (Section.PresheafExtendedScalars.pushedCoefficientScalarComponent (a ≫ g) f ((Scheme.Modules.pullback (a ≫ g)).obj M) r U)
    (Section.PresheafExtendedScalars.pushedCoefficientScalarComponent_coefficient (a ≫ g) f
      ((Scheme.Modules.pullback (a ≫ g)).obj M) r hr U)
    ((Coefficient.PullbackRefinement.coefficientPullbackRefinementMap a g f M).app (op U)).hom

theorem refinementSectionTensorComparisonApp_natural
    {U V : Z.Opens} (h : V ≤ U) (c : C)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))).obj (op U)) :
    refinementSectionTensorComparisonApp a g f M r hr V
        (c ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf f
          ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))).map (homOfLE h).op x) =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward (a ≫ g)).obj
        ((Scheme.Modules.pullback (a ≫ g)).obj M))).map (homOfLE h).op
          (refinementSectionTensorComparisonApp a g f M r hr U (c ⊗ₜ[R] x)) := by
  let α := Coefficient.PullbackRefinement.coefficientPullbackRefinementMap a g f M
  let σ := Section.PresheafExtendedScalars.pushedCoefficientScalarRingHom (a ≫ g) f ((Scheme.Modules.pullback (a ≫ g)).obj M) r c
  have hα := ConcreteCategory.congr_hom (α.naturality (homOfLE h).op) x
  have hσ := ConcreteCategory.congr_hom (σ.naturality (homOfLE h).op) (α.app (op U) x)
  exact (congrArg (fun z => σ.app (op V) z) hα).trans hσ

theorem refinementSectionTensorComparisonApp_value (U : Z.Opens) (c : C)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))).obj (op U)) :
    refinementSectionTensorComparisonApp a g f M r hr U (c ⊗ₜ[R] x) =
      ((Scheme.Modules.pullbackComp a g).hom.app M).app ((a ≫ g) ⁻¹ᵁ U)
        (Module.SectionTensorComparison.moduleSectionTensorComparisonApp a (g.appTop.hom.comp f) ((Scheme.Modules.pullback g).obj M)
          r (SectionTensorValues.sectionTensor_composite_coefficients a g f r hr) (g ⁻¹ᵁ U)
            (c ⊗ₜ[R] (show (Coefficient.ModulePresheaf.coefficientModulePresheaf (g.appTop.hom.comp f)
              ((Scheme.Modules.pullback g).obj M)).obj (op (g ⁻¹ᵁ U)) from x))) := by
  let W := (a ≫ g) ⁻¹ᵁ U
  let K : X.Modules := (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback g).obj M)
  let L : X.Modules := (Scheme.Modules.pullback (a ≫ g)).obj M
  let e : K ⟶ L := (Scheme.Modules.pullbackComp a g).hom.app M
  let z : Γ(K, W) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback g).obj M)).app
      (g ⁻¹ᵁ U) x
  let d : Γ(X, W) := X.presheaf.map W.leTop.op (r c)
  change d • e.app W z = e.app W (d • z)
  exact (e.app_smul d z).symm

theorem refinementSectionTensorComparisonApp_comp_tmul
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = a.appTop.hom.comp q)
    (U : Z.Opens) (c : C) (b : B) (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f M).obj (op U)) :
    refinementSectionTensorComparisonApp a g f M r hr U
      (c ⊗ₜ[R] Module.SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq U (b ⊗ₜ[R] x)) =
        Module.SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ g) f M r hr U
          (sectionTensorCoefficientProduct α (c ⊗ₜ[R] b) ⊗ₜ[R] x) :=
  (refinementSectionTensorComparisonApp_value a g f M r hr U c
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq U (b ⊗ₜ[R] x))).trans
      (SectionTensorValues.moduleSectionTensorComparisonApp_iterated_tmul a g f M q r hq hr α hα U b c x)

variable {ι : Type u} [LinearOrder ι] (U : ι → Z.Opens)

def refinementCechTensorMap :
    Module.TensorFunctor.ModuleTensorFunctor.complex C (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)) U) ⟶
      Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f ((Scheme.Modules.pushforward (a ≫ g)).obj
        ((Scheme.Modules.pullback (a ≫ g)).obj M)) U :=
  OrderedCech.TensorComplex.CechTensorComparison.map C f
    ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))
    ((Scheme.Modules.pushforward (a ≫ g)).obj ((Scheme.Modules.pullback (a ≫ g)).obj M)) U
    (refinementSectionTensorComparisonApp a g f M r hr)
    (fun _ _ i c x => refinementSectionTensorComparisonApp_natural a g f M r hr i.le c x)

theorem coefficientCechTensorPushforwardMap_comp
    (α : B →ₐ[R] C) (hα : r.comp α.toRingHom = a.appTop.hom.comp q) :
    Module.TensorFunctor.ModuleTensorFunctor.map C (Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap g f M q hq U) ≫
        refinementCechTensorMap a g f M r hr U =
      DoubleTensorCochainMap.doubleTensorCochainMap (sectionTensorCoefficientProduct α) (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex f M U) ≫
        Coefficient.SectionTensorModelCriterion.coefficientCechTensorPushforwardMap (a ≫ g) f M r hr U := by
  exact Cech.TensorComparisonComposition.CechTensorComparison.map_comp_tensor B C C f M
    ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))
    ((Scheme.Modules.pushforward (a ≫ g)).obj ((Scheme.Modules.pullback (a ≫ g)).obj M)) U
    (sectionTensorCoefficientProduct α)
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp g f M q hq)
    (refinementSectionTensorComparisonApp a g f M r hr)
    (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (a ≫ g) f M r hr)
    (fun V c b x => refinementSectionTensorComparisonApp_comp_tmul a g f M q r hq hr α hα V c b x)
    (fun _ _ i b x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural g f M q hq i.le b x)
    (fun _ _ i c x => refinementSectionTensorComparisonApp_natural a g f M r hr i.le c x)
    (fun _ _ i c x => Module.SectionTensorNaturality.moduleSectionTensorComparisonApp_natural (a ≫ g) f M r hr i.le c x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.CechTensorPushforward
