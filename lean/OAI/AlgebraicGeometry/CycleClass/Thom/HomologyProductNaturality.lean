import OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity

/-! # Homology Product Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductNaturality

noncomputable section

/-! Naturality and scalar compatibility for homology products induced by
actual chain maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Cycles.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity.Constructions.Products
open scoped TensorProduct

namespace Constructions

variable {k : Type} [Field k]
variable {C D E C' D' E' : ChainComplex (ModuleCat.{0} k) ℕ}

theorem homologyProduct_natural (F : C ⊗ D ⟶ E) (F' : C' ⊗ D' ⟶ E')
    (f : C ⟶ C') (g : D ⟶ D') (u : E ⟶ E')
    (hh : (f ⊗ₘ g) ≫ F' = F ≫ u)
    (p q n : ℕ) (hpq : p + q = n) (a : C.homology p) (b : D.homology q) :
    homologyMap u n (HomologyProductAssociativity.Constructions.Products.homologyProduct F p q n hpq a b) =
      HomologyProductAssociativity.Constructions.Products.homologyProduct F' p q n hpq (homologyMap f p a) (homologyMap g q b) := by
  obtain ⟨x, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C p a
  obtain ⟨y, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective D q b
  simp only [HomologyProductAssociativity.Constructions.Products.homologyProduct_of_cycles, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  have he := congrArg (fun t : C ⊗ D ⟶ E' =>
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap t n (Tensor.Cycles.Constructions.tensorCycleAt C D p q n hpq x y)) hh
  rw [HomologyProductAssociativity.Constructions.Products.cycleMap_comp, Tensor.Cycles.Constructions.tensorCycleAt_natural, HomologyProductAssociativity.Constructions.Products.cycleMap_comp] at he
  exact congrArg (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass E' n) he.symm

theorem homologyProduct_smul_left (F : C ⊗ D ⟶ E)
    (p q n : ℕ) (hpq : p + q = n) (s : k) (a : C.homology p) (b : D.homology q) :
    HomologyProductAssociativity.Constructions.Products.homologyProduct F p q n hpq (s • a) b = s • HomologyProductAssociativity.Constructions.Products.homologyProduct F p q n hpq a b := by
  simp only [HomologyProductAssociativity.Constructions.Products.homologyProduct, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]

theorem homologyProduct_smul_right (F : C ⊗ D ⟶ E)
    (p q n : ℕ) (hpq : p + q = n) (s : k) (a : C.homology p) (b : D.homology q) :
    HomologyProductAssociativity.Constructions.Products.homologyProduct F p q n hpq a (s • b) = s • HomologyProductAssociativity.Constructions.Products.homologyProduct F p q n hpq a b := by
  simp only [HomologyProductAssociativity.Constructions.Products.homologyProduct, TensorProduct.tmul_smul, map_smul]

theorem homologyProduct_cast (F : C ⊗ D ⟶ E)
    (p q n : ℕ) (hpq : p + q = n) (a : C.homology p) (b : D.homology q) :
    HomologyProductAssociativity.Constructions.Products.homologyProduct F p q n hpq a b =
      eqToHom (congrArg (fun j => E.homology j) hpq) (HomologyProductAssociativity.Constructions.Products.homologyProduct F p q (p + q) rfl a b) := by
  subst n
  rfl

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductNaturality
