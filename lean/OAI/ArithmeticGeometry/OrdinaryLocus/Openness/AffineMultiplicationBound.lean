import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineGenericPointCount
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDifferential
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.InseparableDegreeBound
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenChartDimension

/-! # Affine Multiplication Bound -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineMultiplicationBound.Construction

noncomputable section

/-! The finite affine multiplication bound from its total degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj

universe u

theorem geometricPointCard_multiplication_chart_le
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [FaithfulSMul R B] [Module.Finite R B] [Module.Flat R B]
    [Algebra.FinitePresentation R B]
    (i : Spec (.of R) ⟶ A.left) (j : Spec (.of B) ⟶ A.left) [Mono i]
    (hj : j ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ i =
      j ≫ (Multiplication.Construction.multiplicationMap A p).left) (s : Spec (.of R)) :
    let K := (⊥ : Ideal R).ResidueField
    let L := K ⊗[R] B
    letI := (GenericFiberAlgebra.Construction.isField_genericFiberAlgebra R B K).toField
    letI : Algebra k L := Algebra.TensorProduct.leftAlgebra
    ∀ g : ℕ, Module.finrank K L = p ^ (2 * g) →
      Module.finrank L (KaehlerDifferential k L) = g →
      Nat.card (DefinitionsTorsion.geometricPoint (Spec (.of R)) s ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ≤ p ^ g := by
  dsimp only
  let K := (⊥ : Ideal R).ResidueField
  let L := K ⊗[R] B
  let : Field L := (GenericFiberAlgebra.Construction.isField_genericFiberAlgebra R B K).toField
  let : Algebra k L := Algebra.TensorProduct.leftAlgebra
  let : Algebra B L := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k B L := by
    constructor
    intro c b z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      change ((1 : K) ⊗ₜ[R] (c • b)) * (x ⊗ₜ[R] y) =
        c • (((1 : K) ⊗ₜ[R] b) * (x ⊗ₜ[R] y))
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul']
      rw [smul_mul_assoc, ← IsScalarTower.algebraMap_smul R c (b * y),
        ← TensorProduct.smul_tmul, IsScalarTower.algebraMap_smul]
    | add z w hz hw => simp only [smul_add, hz, hw]
  have : CharP K p := charP_of_injective_ringHom (algebraMap k K).injective p
  have : CharP L p := charP_of_injective_ringHom (algebraMap k L).injective p
  intro g hdeg hdim
  have hz := MultiplicationDifferential.Construction.map_kaehler_multiplication_fractionField_eq_zero
    (K := K) (L := L) p A R B i j hj hφ
  exact (AffineGenericPointCount.Construction.geometricPointCard_spec_le_generic_degree R B s).trans
    (InseparableDegreeBound.Construction.finSepDegree_le_pow_of_zero_differential k K L p g hz hdeg hdim)

/-- For an actual affine open chart of an abelian variety, its dimension
supplies the differential dimension, leaving only the total-degree input. -/
theorem geometricPointCard_multiplication_chart_le_of_degree
    {k : Type u} [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [FaithfulSMul R B] [Module.Finite R B] [Module.Flat R B]
    [Algebra.FinitePresentation R B]
    (i : Spec (.of R) ⟶ A.left) (j : Spec (.of B) ⟶ A.left)
    [Mono i] [IsOpenImmersion j]
    (hj : j ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ i =
      j ≫ (Multiplication.Construction.multiplicationMap A p).left)
    (g : ℕ) (hdim : topologicalKrullDim A.left = (g : WithBot ℕ∞))
    (hdegree : Module.rankAtStalk (R := R) B (⊥ : PrimeSpectrum R) = p ^ (2 * g))
    (s : Spec (.of R)) :
    Nat.card (DefinitionsTorsion.geometricPoint (Spec (.of R)) s ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))) ≤ p ^ g := by
  let K := (⊥ : Ideal R).ResidueField
  let L := K ⊗[R] B
  let : Field L := (GenericFiberAlgebra.Construction.isField_genericFiberAlgebra R B K).toField
  let : Algebra k L := Algebra.TensorProduct.leftAlgebra
  let : Algebra B L := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k B L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    change algebraMap k K c ⊗ₜ[R] (1 : B) = 1 ⊗ₜ[R] algebraMap k B c
    rw [IsScalarTower.algebraMap_apply k R K, IsScalarTower.algebraMap_apply k R B]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
  have : IsFractionRing B L := GenericFiberAlgebra.Construction.isFractionRing_genericFiberAlgebra R B K
  have hdim' := (OpenChartDimension.Construction.finrank_fractionField_differentials_of_open_chart A B L j hj).trans hdim
  have hdimNat : Module.finrank L (KaehlerDifferential k L) = g := by
    exact_mod_cast hdim'
  have hdeg : Module.finrank K L = p ^ (2 * g) := by
    rw [Module.rankAtStalk_eq] at hdegree
    exact hdegree
  exact geometricPointCard_multiplication_chart_le p A R B i j hj hφ s g hdeg hdimNat

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineMultiplicationBound.Construction
