import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor

/-! # Extension Quasi Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ExtensionQuasiIso

noncomputable section

/-! Universal tensor quasi-isomorphisms remain quasi-isomorphisms as complexes over each extended coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

def scalarExtensionRestrictionIso : HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (R := R) A ≅
    Cochain.ScalarExtensionKernel.moduleScalarExtensionFunctor A ⋙ ModuleCat.restrictScalars (algebraMap R A) := by
  refine NatIso.ofComponents (fun M => ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext z
    let z' : A ⊗[R] (↥M) := z
    change algebraMap R A r • z' = r • z'
    exact IsScalarTower.algebraMap_smul A r z'
  · intro M N a
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext s m
    rfl

def scalarExtensionRestrictionComplexIso :
    (Cochain.ScalarExtensionKernel.moduleScalarExtensionFunctor (R := R) A).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      (ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℕ) ≅
        (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (R := R) A).mapHomologicalComplex (ComplexShape.up ℕ) :=
  Functor.mapHomologicalComplexCompIso (scalarExtensionRestrictionIso A).symm (ComplexShape.up ℕ)

theorem scalarExtension_quasiIso_of_universal_tensor
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)
    (h : ∀ (B : Type u) [AddCommGroup B] [Module R B], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B φ)) :
    QuasiIso (((Cochain.ScalarExtensionKernel.moduleScalarExtensionFunctor A).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) := by
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ) := h A
  let e := scalarExtensionRestrictionComplexIso (R := R) A
  let ψ := ((Cochain.ScalarExtensionKernel.moduleScalarExtensionFunctor A).mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  let χ := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℕ)).map ψ
  let a : Arrow.mk χ ≅ Arrow.mk (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ) :=
    Arrow.isoMk (e.app C) (e.app D) (e.hom.naturality φ)
  have hχ : QuasiIso χ :=
    (quasiIso_iff_of_arrow_mk_iso χ (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ) a).mpr inferInstance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology ψ
    (ModuleCat.restrictScalars (algebraMap R A))).mp hχ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.ExtensionQuasiIso
