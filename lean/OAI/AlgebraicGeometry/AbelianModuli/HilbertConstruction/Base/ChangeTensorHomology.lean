import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # Change Tensor Homology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorHomology

noncomputable section

/-! The actual B-linear base-change complex and the underlying R-linear tensor complex have canonically isomorphic homology after restriction. A surjective coefficient map lifts such restricted isomorphisms to B-linear equivalences. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

def moduleBaseChangeRestrictionIso :
    Module.TensorFunctor.ModuleTensorFunctor.tensor (R := R) B ≅
      Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B ⋙ ModuleCat.restrictScalars (algebraMap R B) := by
  refine NatIso.ofComponents (fun M => ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro r
    ext z
    change B ⊗[R] M at z
    change (algebraMap R B r) • z = r • z
    exact IsScalarTower.algebraMap_smul B r z
  · intro M N f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext b m
    rfl

def baseChangeTensorHomologyIso (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R B)).obj
      ((((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).homology q) ≅
        (Module.TensorFunctor.ModuleTensorFunctor.complex B C).homology q := by
  let BC := ((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C
  let e := Functor.mapHomologicalComplexCompIso
    (moduleBaseChangeRestrictionIso (R := R) (B := B)).symm (.up ℕ)
  exact ((BC.sc q).mapHomologyIso (ModuleCat.restrictScalars (algebraMap R B))).symm ≪≫
    HomologicalComplex.homologyMapIso (e.app C) q

def restrictedModuleIsoLinearEquiv
    (f : R →+* B) (hf : Function.Surjective f) {M N : ModuleCat.{u} B}
    (e : (ModuleCat.restrictScalars f).obj M ≅ (ModuleCat.restrictScalars f).obj N) :
    M ≃ₗ[B] N where
  toFun x := e.hom x
  invFun y := e.inv y
  left_inv := e.toLinearEquiv.left_inv
  right_inv := e.toLinearEquiv.right_inv
  map_add' := e.toLinearEquiv.map_add
  map_smul' b x := by
    obtain ⟨r, rfl⟩ := hf b
    exact e.toLinearEquiv.map_smul r x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorHomology
