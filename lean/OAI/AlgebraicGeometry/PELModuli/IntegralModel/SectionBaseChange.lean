import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CechPullbackSectionNormalization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.KernelMap
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GlobalModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModelOneTensor

/-! # Section Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SectionBaseChange

noncomputable section

/-! A degree-zero model gives the actual base-change map on global
sections, normalized on pure tensors. Exactness of the kernel sequence
after base change makes this canonical map surjective. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

variable {X Y S T : Scheme.{u}} (a : Y ⟶ X) (f : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : a ≫ f = ρ ≫ g) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ}
variable (φ : D ⟶ SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex f M U)
variable [QuasiIsoAt φ 0] [QuasiIsoAt (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a f ρ g h M U φ) 0]

theorem modelKernelSections_one (m : (D.d 0 1).hom.ker) :
    Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h M U hU φ (Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g m) =
      CechPullbackSectionNormalization.pullbackTopSection a M (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f M U hU φ m) := by
  let V := fun i => a ⁻¹ᵁ U i
  have hV : iSup V = ⊤ := by rw [← a.preimage_iSup, hU]; rfl
  let e := Quotients.FiniteDescent.OrderedCechZeroGluing.Construction.OrderedCechZeroCoordinates.sectionsEquiv ρ ((Scheme.Modules.pullback a).obj M) V hV
  let k := Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (Quotients.FiniteDescent.CechModelBaseChange.Construction.CechBaseChangeMap.modelMap a f ρ g h M U φ)
  change e.symm (k (Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g m)) = _
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change (k (Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g m)).val =
    Quotients.FiniteDescent.OrderedCechSquare.Construction.OrderedCechAugmentation.map ρ ((Scheme.Modules.pullback a).obj M) V
      (CechPullbackSectionNormalization.pullbackTopSection a M (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f M U hU φ m))
  rw [Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]
  exact (Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.model_one a f ρ g h M U φ 0 m.val).trans
    ((congrArg (fun z => (Quotients.FiniteDescent.CechBaseTmul.Construction.CechBaseChangeMap.restrictedMap a f ρ g h M U).f 0 z)
      (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.coordinate f M U hU φ m)).trans
        (CechPullbackSectionNormalization.cech_restricted_global_eq_pullback a f ρ g h M U _))

def modelSectionsBaseChangeMap :
    (ModuleCat.extendScalars g.appTop.hom).obj ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op ⊤)) ⟶
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback a).obj M)).obj (op ⊤) :=
  (ModuleCat.extendScalars g.appTop.hom).map
      (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f M U hU φ).symm.toModuleIso.hom ≫
    ModuleCat.ofHom (Scalar.KernelMap.scalarKernelMap g.appTop.hom (D.d 0 1)) ≫
      (Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h M U hU φ).toModuleIso.hom

theorem modelSectionsBaseChangeMap_one (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op ⊤)) :
    modelSectionsBaseChangeMap a f ρ g h M U hU φ ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
      CechPullbackSectionNormalization.pullbackTopSection a M s := by
  let m := (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f M U hU φ).symm s
  have he : Scalar.KernelMap.scalarKernelMap g.appTop.hom (D.d 0 1)
      ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m) = Quotients.FiniteDescent.ModelOneTensor.Construction.CechBaseChangeMap.oneCycle g m :=
    Subtype.ext (Scalar.KernelMap.scalarKernelMap_one_val g.appTop.hom (D.d 0 1) m)
  change Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h M U hU φ
    (Scalar.KernelMap.scalarKernelMap g.appTop.hom (D.d 0 1)
      ((ModuleCat.extendScalars g.appTop.hom).map
        (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f M U hU φ).symm.toModuleIso.hom
          ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s))) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  change Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h M U hU φ
    (Scalar.KernelMap.scalarKernelMap g.appTop.hom (D.d 0 1) ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)) = _
  rw [he, modelKernelSections_one]
  exact congrArg (CechPullbackSectionNormalization.pullbackTopSection a M) ((Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f M U hU φ).apply_symm_apply s)

theorem modelSectionsBaseChangeMap_surjective
    (hex : ((D.d 0 1).hom.shortComplexKer.map (ModuleCat.extendScalars g.appTop.hom)).Exact) :
    Function.Surjective (modelSectionsBaseChangeMap a f ρ g h M U hU φ) := by
  exact (Quotients.FiniteDescent.CechModelSections.Construction.CechBaseChangeMap.kernelSections a f ρ g h M U hU φ).surjective.comp
    ((Scalar.KernelMap.scalarKernelMap_surjective g.appTop.hom (D.d 0 1) hex).comp
      (ConcreteCategory.bijective_of_isIso ((ModuleCat.extendScalars g.appTop.hom).map
        (Quotients.FiniteDescent.GlobalModel.Construction.GlobalModelSections.equiv f M U hU φ).symm.toModuleIso.hom)).surjective)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SectionBaseChange
