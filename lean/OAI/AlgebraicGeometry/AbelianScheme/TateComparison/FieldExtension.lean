import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldExtensionPoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LevelEquivalence
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group

/-! # Field Extension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldExtension

noncomputable section

/-! Field extension over an algebraically closed characteristic-zero
field induces an isomorphism of the actual integral Tate modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K k : Type} [Field K] [Field k]
  (b : Spec (.of k) ⟶ Spec (.of K))
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
  (q : ℕ) [Fact q.Prime]

def fieldPointAddMap :
    Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ A) →+ Additive (Over.mk b ⟶ A) :=
  (FieldExtensionPoints.fieldPointMap b A).toAdditive

theorem fieldTorsionMap_injective (n : ℕ) :
    Function.Injective (Add.Tate.mapLevel q (fieldPointAddMap b A) n) := by
  intro x y h
  apply Subtype.ext
  apply Additive.toMul.injective
  apply FieldExtensionPoints.fieldPointMap_injective b A
  exact congrArg (fun z : Add.Tate.torsion q (Additive (Over.mk b ⟶ A)) n => z.val.toMul) h

theorem finiteEtale_fieldTorsionMap_surjective [IsSepClosed K] (n : ℕ)
    [IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A (q ^ n)).hom]
    [Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A (q ^ n)).hom] :
    Function.Surjective (Add.Tate.mapLevel q (fieldPointAddMap b A) n) := by
  intro z
  have hz : z.val.toMul ^ (q ^ n) = 1 := congrArg Additive.toMul z.property
  let p := TorsionQuotient.SubgroupFunctor.torsionLift (q ^ n) z.val.toMul hz
  obtain ⟨w, hw⟩ := FieldExtensionPoints.finiteEtale_fieldPointMap_surjective b (TorsionQuotient.SubgroupFunctor.torsionScheme A (q ^ n)) p
  let y : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ A)) n :=
    ⟨Additive.ofMul (w ≫ TorsionQuotient.SubgroupFunctor.torsionι A (q ^ n)), by
      apply Additive.toMul.injective
      exact (TorsionQuotient.Group.TorsionGroup.pointsEquiv A (q ^ n) _ w).property⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  change FieldExtensionPoints.fieldTestMap b ≫ (w ≫ TorsionQuotient.SubgroupFunctor.torsionι A (q ^ n)) = z.val.toMul
  rw [← Category.assoc]
  change FieldExtensionPoints.fieldPointMap b (TorsionQuotient.SubgroupFunctor.torsionScheme A (q ^ n)) w ≫ TorsionQuotient.SubgroupFunctor.torsionι A (q ^ n) = _
  rw [hw]
  exact TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _

def fieldTateMap :
    Add.schemeTateModule A (Over.mk (𝟙 (Spec (.of K)))) q →ₗ[ℤ_[q]]
      Add.schemeTateModule A (Over.mk b) q :=
  Add.Tate.map q (fieldPointAddMap b A)

theorem fieldTateMap_natural {B : Over (Spec (.of K))} [GrpObj B] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] :
    (fieldTateMap b B q).comp (Add.schemeTateMap A (Over.mk (𝟙 (Spec (.of K)))) q f) =
      (Add.schemeTateMap A (Over.mk b) q f).comp (fieldTateMap b A q) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact congrArg Additive.ofMul
    (Category.assoc (FieldExtensionPoints.fieldTestMap b) (z.val n).val.toMul f).symm

variable [CharZero K] [IsAlgClosed K] {g : ℕ}
  (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))

theorem abelian_fieldTateMap_bijective : Function.Bijective (fieldTateMap b G.scheme q) := by
  apply LevelEquivalence.Tate.map_bijective_of_levels
  intro n
  have hn := TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale G.scheme (q ^ n)
    (GeometricDivision.field_integer_unit_at_stalk (q ^ n))
  have := hn.1
  have := hn.2
  exact ⟨fieldTorsionMap_injective b G.scheme q n,
    finiteEtale_fieldTorsionMap_surjective b G.scheme q n⟩

def abelianFieldTateEquiv :
    Add.schemeTateModule G.scheme (Over.mk (𝟙 (Spec (.of K)))) q ≃ₗ[ℤ_[q]]
      Add.schemeTateModule G.scheme (Over.mk b) q :=
  LinearEquiv.ofBijective (fieldTateMap b G.scheme q) (abelian_fieldTateMap_bijective b q G)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldExtension
