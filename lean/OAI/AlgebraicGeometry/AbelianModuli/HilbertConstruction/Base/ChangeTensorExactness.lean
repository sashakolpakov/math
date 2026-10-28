import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Change Tensor Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorExactness

noncomputable section

/-! The native B-linear base-change complex and the R-linear tensor complex have identical exactness, because their differentials have the same underlying functions. -/
open _root_.CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

theorem baseChange_shortComplex_exact_iff_tensor (S : ShortComplex (ModuleCat.{u} R)) :
    (Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B S).Exact ↔
      (S.map (Module.TensorFunctor.ModuleTensorFunctor.tensor B)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  change (∀ x, S.g.hom.baseChange B x = 0 → ∃ y, S.f.hom.baseChange B y = x) ↔
    (∀ x, S.g.hom.lTensor B x = 0 → ∃ y, S.f.hom.lTensor B y = x)
  constructor
  · intro h x hx
    obtain ⟨y, hy⟩ := h x ((congrFun (LinearMap.baseChange_eq_ltensor (A := B) S.g.hom) x).trans hx)
    exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor (A := B) S.f.hom) y).symm.trans hy⟩
  · intro h x hx
    obtain ⟨y, hy⟩ := h x ((congrFun (LinearMap.baseChange_eq_ltensor (A := B) S.g.hom) x).symm.trans hx)
    exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor (A := B) S.f.hom) y).trans hy⟩

theorem baseChange_exactAt_iff_tensor (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    (((Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R B).mapHomologicalComplex (.up ℕ)).obj C).ExactAt q ↔
      (Module.TensorFunctor.ModuleTensorFunctor.complex B C).ExactAt q :=
  baseChange_shortComplex_exact_iff_tensor (B := B) (C.sc q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangeTensorExactness
