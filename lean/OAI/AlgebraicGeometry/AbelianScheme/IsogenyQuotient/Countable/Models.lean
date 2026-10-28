import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.CoefficientFields
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.AbelianModel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons

/-! # Models -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Models.Construction

noncomputable section

/-! Finitely many projectively presented geometric abelian schemes
have full group models over one countable algebraically closed subfield
of the original field, with their actual base-change isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.AbelianModel

structure CountableAbelianFamilyModel
    {k : Type} [Field k] {I : Type} (g : I → ℕ)
    (A : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (g i) (Spec (.of k))) where
  field : Subfield k
  [countable : Countable field]
  [algebraicallyClosed : IsAlgClosed field]
  family : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (g i) (Spec (.of field))
  recovery : ∀ i, (A i).scheme ≅
    ((family i).pullback (Spec.map (CommRingCat.ofHom field.subtype))).scheme
  recovery_group : ∀ i, IsMonHom (recovery i).hom

attribute [instance] CountableAbelianFamilyModel.countable
  CountableAbelianFamilyModel.algebraicallyClosed CountableAbelianFamilyModel.recovery_group

set_option backward.isDefEq.respectTransparency false in
theorem countable_abelian_family_model_exists
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
    {I : Type} [Finite I] (g : I → ℕ)
    (A : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (g i) (Spec (.of k))) (n : I → ℕ)
    (D : ∀ i, AbelianModuli.ReferenceFamily.Geometric.GroupModel.GeometricGroupModel (A i).scheme (n i)) :
    Nonempty (CountableAbelianFamilyModel g A) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let s := Finset.univ.biUnion (fun i => (D i).data.toModel.coefficients)
  let R := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k s
  have : Algebra.FiniteType ℚ R := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing_finiteType ℚ k s
  have : Countable R := TateComparison.CountableResidueFields.countable_finiteType ℚ R
  obtain ⟨F, hF, ha, hRF⟩ := CoefficientFields.Construction.countable_algebraicallyClosed_subfield_of_coefficients R
  let : Countable F := hF
  let : IsAlgClosed F := ha
  let b := Spec.map (CommRingCat.ofHom F.subtype)
  have hi (i : I) : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k (D i).data.toModel.coefficients ≤ R :=
    Algebra.adjoin_mono (Finset.coe_subset.mpr
      (Finset.subset_biUnion_of_mem (fun i => (D i).data.toModel.coefficients) (Finset.mem_univ i)))
  let j (i : I) : ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k (D i).data.toModel.coefficients →+* F :=
    (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ k (D i).data.toModel.coefficients).val.toRingHom.codRestrict F
      (fun r => hRF ⟨r.val, hi i r.property⟩)
  let v (i : I) := Spec.map (CommRingCat.ofHom (j i))
  have hv (i : I) : b ≫ v i = ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k (D i).data.toModel.coefficients := by
    rw [← Spec.map_comp]
    rfl
  let C (i : I) := AbelianModuli.ReferenceFamily.Geometric.GroupModel.GeometricGroupModel.abelian (A i) (D i)
  let B (i : I) := (C i).pullback (v i)
  let groupV (i : I) : GrpObj ((Over.pullback (v i)).obj (C i).scheme) := (B i).group
  let groupBV (i : I) : GrpObj ((Over.pullback b).obj ((Over.pullback (v i)).obj (C i).scheme)) :=
    ((B i).pullback b).group
  let groupGeneric (i : I) : GrpObj ((Over.pullback
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k (D i).data.toModel.coefficients)).obj (C i).scheme) :=
    ((C i).pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k (D i).data.toModel.coefficients)).group
  let r (i : I) : ((B i).pullback b).scheme ≅ (A i).scheme :=
    PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (C i).scheme (v i) b
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k (D i).data.toModel.coefficients) (hv i) ≪≫
        AbelianModuli.ReferenceFamily.Geometric.GroupModel.GeometricGroupModel.fiberIso (A i) (D i)
  have hr (i : I) : IsMonHom (r i).hom := by
    have h₁ := PELModuli.IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom (C i).scheme (v i) b
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ k (D i).data.toModel.coefficients) (hv i)
    have h₂ := AbelianModuli.ReferenceFamily.Geometric.GroupModel.GeometricGroupModel.fiberIso_isMonHom (A i) (D i)
    exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h₁ h₂
  exact ⟨{
    field := F
    family := B
    recovery := fun i => (r i).symm
    recovery_group := fun i => by
      have := hr i
      exact inferInstanceAs (IsMonHom (r i).inv) }⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.Models.Construction
