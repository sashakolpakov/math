import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorProducts
import Mathlib.Algebra.Homology.QuasiIso

/-! # Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Extension.TensorExtension

noncomputable section

/-! Universal tensor comparisons also give comparisons after extension of scalars. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

def iso : letI : Algebra R S := f.toAlgebra
    HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (R := R) S ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f := by
  letI : Algebra R S := f.toAlgebra
  refine NatIso.ofComponents (fun M => ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext z
    let z' : S ⊗[R] (↥M) := z
    change f r • z' = r • z'
    exact IsScalarTower.algebraMap_smul S r z'
  · intro M N a
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext s m
    rfl

def complexIso : letI : Algebra R S := f.toAlgebra
    (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      (ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ) ≅
        (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor (R := R) S).mapHomologicalComplex (ComplexShape.up ℕ) := by
  letI : Algebra R S := f.toAlgebra
  exact Functor.mapHomologicalComplexCompIso (iso f).symm (ComplexShape.up ℕ)

theorem quasiIso {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)
    (h : ∀ (A : Type u) [AddCommGroup A] [Module R A], QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ)) :
    QuasiIso (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) := by
  let : Algebra R S := f.toAlgebra
  have : QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map S φ) := h S
  let e := complexIso f
  let ψ := ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  let χ := ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).map ψ
  let a : Arrow.mk χ ≅ Arrow.mk (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map S φ) :=
    Arrow.isoMk (e.app C) (e.app D) (e.hom.naturality φ)
  have hχ : QuasiIso χ :=
    (quasiIso_iff_of_arrow_mk_iso χ (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map S φ) a).mpr inferInstance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology ψ
    (ModuleCat.restrictScalars f)).mp hχ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Extension.TensorExtension
