import OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe

/-! # Tensor Zero -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorZero.Constructions

noncomputable section

/-! Zero maps in either factor give zero maps of the genuine tensor complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex

variable {k : Type} [Field k]
variable {C C' D D' : ChainComplex (ModuleCat.{0} k) ℕ}

theorem tensorChainHom_zero_left (f : D ⟶ D') : (0 : C ⟶ C') ⊗ₘ f = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q hpq
  have hi := AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom
    C D (0 : C ⟶ C') f n ⟨(p,q), hpq⟩
  change ιTensorObj C D p q n hpq ≫ ((0 : C ⟶ C') ⊗ₘ f).f n =
    (0 ⊗ₘ f.f q) ≫ ιTensorObj C' D' p q n hpq at hi
  rw [MonoidalPreadditive.zero_tensor (f.f q), zero_comp] at hi
  exact hi.trans comp_zero.symm

theorem tensorChainHom_zero_right (f : C ⟶ C') : f ⊗ₘ (0 : D ⟶ D') = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q hpq
  have hi := AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom
    C D f (0 : D ⟶ D') n ⟨(p,q), hpq⟩
  change ιTensorObj C D p q n hpq ≫ (f ⊗ₘ (0 : D ⟶ D')).f n =
    (f.f p ⊗ₘ 0) ≫ ιTensorObj C' D' p q n hpq at hi
  rw [MonoidalPreadditive.tensor_zero (f.f p), zero_comp] at hi
  exact hi.trans comp_zero.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorZero.Constructions
