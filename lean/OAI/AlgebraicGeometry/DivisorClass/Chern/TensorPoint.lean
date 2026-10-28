import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorBoundary
import OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe

/-! # Tensor Point -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorPoint

noncomputable section

section

/-!
# ChernClass: crossing with an actual degree-zero chain

A zero-chain gives a chain map into the tensor complex. The map is
natural in both chain complexes and carries exactly the specified
zero-chain under the left factor map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type} [Field k]

def tensorPointChain (C D : ChainComplex (ModuleCat.{0} k) ℕ) (x : C.X 0) :
    D ⟶ C ⊗ D where
  f n := ModuleCat.ofHom ((ιTensorObj C D 0 n n (by omega)).hom.comp
    (TensorProduct.mk k (C.X 0) (D.X n) x))
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact TensorBoundary.tensorBoundary_point_apply C D j x y

@[simp]
theorem tensorPointChain_apply (C D : ChainComplex (ModuleCat.{0} k) ℕ)
    (x : C.X 0) (n : ℕ) (y : D.X n) :
    (tensorPointChain C D x).f n y = ιTensorObj C D 0 n n (by omega) (x ⊗ₜ[k] y) := rfl

theorem tensorPointChain_naturality
    {C C' D D' : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (x : C.X 0) :
    tensorPointChain C D x ≫ (f ⊗ₘ g) =
      g ≫ tensorPointChain C' D' (f.f 0 x) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom C D f g n ⟨(0, n), by omega⟩)
    (x ⊗ₜ[k] y)
  change (HomologicalComplex.tensorHom f g).f n (ιTensorObj C D 0 n n _ _) =
    ιTensorObj C' D' 0 n n _ (TensorProduct.map (f.f 0).hom (g.f n).hom _) at h
  change (HomologicalComplex.tensorHom f g).f n (ιTensorObj C D 0 n n _ (x ⊗ₜ[k] y)) =
    ιTensorObj C' D' 0 n n _ (f.f 0 x ⊗ₜ[k] g.f n y)
  simpa only [TensorProduct.map_tmul] using h

end

/-! The actual tensor chain map with a specified point in the right factor. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type} [Field k]

def tensorRightPointChain (C D : ChainComplex (ModuleCat.{0} k) ℕ) (y : D.X 0) :
    C ⟶ C ⊗ D where
  f n := ModuleCat.ofHom ((ιTensorObj C D n 0 n (by omega)).hom.comp
    ((TensorProduct.mk k (C.X n) (D.X 0)).flip y))
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (C ⊗ D).d (j + 1) j (ιTensorObj C D (j + 1) 0 (j + 1) _ (x ⊗ₜ[k] y)) =
      ιTensorObj C D j 0 j _ (C.d (j + 1) j x ⊗ₜ[k] y)
    have h := ConcreteCategory.congr_hom (TensorBoundary.tensorBoundary_rightZero C D j) (x ⊗ₜ[k] y)
    change (C ⊗ D).d (j + 1) j (ιTensorObj C D (j + 1) 0 (j + 1) _ (x ⊗ₜ[k] y)) =
      ιTensorObj C D j 0 j _ (TensorProduct.map (C.d (j + 1) j).hom LinearMap.id (x ⊗ₜ[k] y)) at h
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply] using h

theorem tensorRightPointChain_naturality
    {C C' D D' : ChainComplex (ModuleCat.{0} k) ℕ}
    (f : C ⟶ C') (g : D ⟶ D') (y : D.X 0) :
    tensorRightPointChain C D y ≫ (f ⊗ₘ g) =
      f ≫ tensorRightPointChain C' D' (g.f 0 y) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom C D f g n ⟨(n, 0), by omega⟩)
    (x ⊗ₜ[k] y)
  change (HomologicalComplex.tensorHom f g).f n (ιTensorObj C D n 0 n _ _) =
    ιTensorObj C' D' n 0 n _ (TensorProduct.map (f.f n).hom (g.f 0).hom _) at h
  change (HomologicalComplex.tensorHom f g).f n (ιTensorObj C D n 0 n _ (x ⊗ₜ[k] y)) =
    ιTensorObj C' D' n 0 n _ (f.f n x ⊗ₜ[k] g.f 0 y)
  simpa only [TensorProduct.map_tmul] using h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorPoint
