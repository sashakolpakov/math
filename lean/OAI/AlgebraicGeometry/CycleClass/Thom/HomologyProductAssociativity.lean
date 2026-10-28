import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Cycles

/-! # Homology Product Associativity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity

noncomputable section

section

/-! Products induced by actual chain maps, with explicit homogeneous degrees.
Associativity follows from a homotopy between the two actual chain composites. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.Add.Construction
open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Cycles.Constructions
open scoped TensorProduct DirectSum

namespace Constructions.Products

variable {k : Type} [Field k]
variable {C D E T : ChainComplex (ModuleCat.{0} k) ℕ}

def homologyProduct (F : C ⊗ D ⟶ E) (p q n : ℕ) (hpq : p + q = n)
    (a : C.homology p) (b : D.homology q) : E.homology n :=
  homologyMap F n (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D n
    (DirectSum.lof k (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs n)
      (fun d => C.homology d.val.1 ⊗[k] D.homology d.val.2) ⟨(p, q), hpq⟩ (a ⊗ₜ[k] b)))

theorem homologyProduct_of_cycles (F : C ⊗ D ⟶ E) (p q n : ℕ) (hpq : p + q = n)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    homologyProduct F p q n hpq (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C p x) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass D q y) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass E n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap F n (Tensor.Cycles.Constructions.tensorCycleAt C D p q n hpq x y)) := by
  rw [homologyProduct, DivisorClass.Chern.TensorArbitraryRepresentatives.algebraicKunneth_of_tensor_cycle C D n ⟨(p, q), hpq⟩ x y
    (Tensor.Cycles.Constructions.tensorCycleAt C D p q n hpq x y) rfl, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]

theorem homologyProduct_comp (F : C ⊗ D ⟶ E) (G : E ⟶ T)
    (p q n : ℕ) (hpq : p + q = n) (a : C.homology p) (b : D.homology q) :
    homologyProduct (F ≫ G) p q n hpq a b =
      homologyMap G n (homologyProduct F p q n hpq a b) := by
  simp only [homologyProduct, homologyMap_comp, ModuleCat.comp_apply]

@[simp]
theorem cycleMap_id (p : ℕ) (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) : AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (𝟙 C) p x = x := by
  apply Subtype.ext
  rfl

theorem cycleMap_comp (F : C ⟶ D) (G : D ⟶ E) (p : ℕ) (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (F ≫ G) p x = AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap G p (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap F p x) := by
  apply Subtype.ext
  rfl

end Constructions.Products

end

/-! Associativity on actual homology classes from an actual chain homotopy. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.Cycles.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity.Constructions.Products

namespace Constructions

variable {k : Type} [Field k]
variable {C D E CD DE T : ChainComplex (ModuleCat.{0} k) ℕ}
variable (F : C ⊗ D ⟶ CD) (G : CD ⊗ E ⟶ T) (H : D ⊗ E ⟶ DE) (I : C ⊗ DE ⟶ T)
variable (p q r n : ℕ) (h : (p + q) + r = n)
variable (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C p) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles E r)

theorem leftComposite_cycle :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((F ⊗ₘ 𝟙 E) ≫ G) n
      (Tensor.Cycles.Constructions.tensorCycleAt (C ⊗ D) E (p + q) r n h (Tensor.Cycles.Constructions.tensorCycleAt C D p q (p + q) rfl x y) z) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap G n (Tensor.Cycles.Constructions.tensorCycleAt CD E (p + q) r n h
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap F (p + q) (Tensor.Cycles.Constructions.tensorCycleAt C D p q (p + q) rfl x y)) z) := by
  rw [Products.cycleMap_comp, Tensor.Cycles.Constructions.tensorCycleAt_natural, Products.cycleMap_id]

theorem rightComposite_cycle :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((α_ C D E).hom ≫ (𝟙 C ⊗ₘ H) ≫ I) n
      (Tensor.Cycles.Constructions.tensorCycleAt (C ⊗ D) E (p + q) r n h (Tensor.Cycles.Constructions.tensorCycleAt C D p q (p + q) rfl x y) z) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap I n (Tensor.Cycles.Constructions.tensorCycleAt C DE p (q + r) n ((Nat.add_assoc p q r).symm.trans h) x
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap H (q + r) (Tensor.Cycles.Constructions.tensorCycleAt D E q r (q + r) rfl y z))) := by
  rw [Products.cycleMap_comp, Tensor.Cycles.Constructions.tensorCycleAt_associator, Products.cycleMap_comp, Tensor.Cycles.Constructions.tensorCycleAt_natural, Products.cycleMap_id]

theorem homologyProduct_associative
    (hh : Homotopy ((F ⊗ₘ 𝟙 E) ≫ G) ((α_ C D E).hom ≫ (𝟙 C ⊗ₘ H) ≫ I))
    (a : C.homology p) (b : D.homology q) (c : E.homology r) :
    Products.homologyProduct G (p + q) r n h (Products.homologyProduct F p q (p + q) rfl a b) c =
      Products.homologyProduct I p (q + r) n ((Nat.add_assoc p q r).symm.trans h) a
        (Products.homologyProduct H q r (q + r) rfl b c) := by
  obtain ⟨x, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective C p a
  obtain ⟨y, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective D q b
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective E r c
  simp only [Products.homologyProduct_of_cycles]
  have he := ConcreteCategory.congr_hom (hh.homologyMap_eq n)
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass ((C ⊗ D) ⊗ E) n
      (Tensor.Cycles.Constructions.tensorCycleAt (C ⊗ D) E (p + q) r n h (Tensor.Cycles.Constructions.tensorCycleAt C D p q (p + q) rfl x y) z))
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    leftComposite_cycle F G p q r n h x y z, rightComposite_cycle H I p q r n h x y z] at he
  exact he

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity
