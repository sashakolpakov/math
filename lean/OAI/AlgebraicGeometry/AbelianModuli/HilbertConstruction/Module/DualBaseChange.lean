import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeDualBaseChange

/-! # Dual Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualBaseChange

noncomputable section

/-! Duals of finite free modules commute with the actual scalar extension. The comparison respects differentials, so exactness of a field fiber passes to the reversed dual short complex. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]
variable (B : Type u) [CommRing B] [Algebra R B]

def moduleDualBaseChangeEquiv
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] :
    B ⊗[R] Module.Dual R M ≃ₗ[B] Module.Dual B (B ⊗[R] M) :=
  HilbertConstruction.Finite.FreeDualBaseChange.IsBaseChange.toDualBaseChange (TensorProduct.isBaseChange R M B)

theorem moduleDualBaseChangeEquiv_tmul_one
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    (b : B) (ℓ : Module.Dual R M) (m : M) :
    moduleDualBaseChangeEquiv (R := R) B M (b ⊗ₜ[R] ℓ) (1 ⊗ₜ[R] m) =
      b * algebraMap R B (ℓ m) :=
  HilbertConstruction.Finite.FreeDualBaseChange.IsBaseChange.toDualBaseChange_tmul (TensorProduct.isBaseChange R M B) b ℓ m

theorem moduleDualBaseChangeEquiv_tmul_tmul
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    (b b' : B) (ℓ : Module.Dual R M) (m : M) :
    moduleDualBaseChangeEquiv (R := R) B M (b ⊗ₜ[R] ℓ) (b' ⊗ₜ[R] m) =
      b' * (b * algebraMap R B (ℓ m)) := by
  have he : b' ⊗ₜ[R] m = b' • (1 ⊗ₜ[R] m : B ⊗[R] M) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [he, map_smul, moduleDualBaseChangeEquiv_tmul_one]
  rfl

theorem moduleDualBaseChangeEquiv_naturality
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N) :
    (moduleDualBaseChangeEquiv (R := R) B M).toLinearMap.comp (f.dualMap.baseChange B) =
      (f.baseChange B).dualMap.comp (moduleDualBaseChangeEquiv (R := R) B N).toLinearMap := by
  ext b ℓ
  simp [moduleDualBaseChangeEquiv_tmul_tmul]

def dualShortComplexBaseChangeIso (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃] :
    BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B (DualFunctor.dualModuleShortComplex S) ≅
      DualFunctor.dualModuleShortComplex (BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B S) :=
  ShortComplex.isoMk (moduleDualBaseChangeEquiv (R := R) B S.X₃).toModuleIso
    (moduleDualBaseChangeEquiv (R := R) B S.X₂).toModuleIso (moduleDualBaseChangeEquiv (R := R) B S.X₁).toModuleIso
    (ModuleCat.hom_ext (moduleDualBaseChangeEquiv_naturality (R := R) B S.g.hom).symm)
    (ModuleCat.hom_ext (moduleDualBaseChangeEquiv_naturality (R := R) B S.f.hom).symm)

theorem field_baseChange_dualShortComplex_exact
    {F : Type u} [Field F] [Algebra R F] (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    (hS : (BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R F S).Exact) :
    (BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R F (DualFunctor.dualModuleShortComplex S)).Exact :=
  (ShortComplex.exact_iff_of_iso (dualShortComplexBaseChangeIso F S)).mpr
    (DualFunctor.field_dualModuleShortComplex_exact _ hS)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.DualBaseChange
