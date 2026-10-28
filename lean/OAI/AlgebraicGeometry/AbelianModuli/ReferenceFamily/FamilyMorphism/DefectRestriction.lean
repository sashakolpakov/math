import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RetractionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.GroupRetractions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.ConormalDeformedSquare

/-! # Defect Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.DefectRestriction

noncomputable section

/-! The actual local family-morphism defects agree under restriction
of both affine subfamilies. Their conormal values restrict by the
original fixed-fiber tensor map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver
attribute [local irreducible] Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction GroupRetractions.familyMorphismGroupRetraction
attribute [local irreducible] Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom] [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]
    (f : X ⟶ Y) (V V' U : X.left.affineOpens) (W W' Z : Y.left.affineOpens)
    (t : V'.1 ≤ V.1) (s : W'.1 ≤ W.1)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (h' : V'.1 ≤ f.left ⁻¹ᵁ W'.1)
    (a : V.1 ≤ U.1) (b : W.1 ≤ Z.1) (d : Derivation ℂ R ℂ)

theorem familyMorphismConormalDefect_restrict
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    GroupRetractions.familyMorphismConormalDefect R f V' U W' Z h' (t.trans a) (s.trans b) d z =
      FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X t (GroupRetractions.familyMorphismConormalDefect R f V U W Z h a b d z) := by
  let C := ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V
  let D := ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V'
  let q := FixedFiber.DerivationPresheaf.fixedFiberTensorRestriction R ℂ X t
  let n := Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates ℂ R X t d
  let m := Dual.TensorMapCoordinates.dualTensorMapCoordinates n
  let M := Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber C) (DualNumber D) m
  let F : TangentBasePoint.fixedFamilyFiber ℂ R X ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f
  let c := (Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X a d).val ≫ F
  let c' := (Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X (t.trans a) d).val ≫ F
  let u : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ c} :=
    ⟨(GroupRetractions.familyMorphismGroupRetraction R f V W Z h b d).val,
      GroupRetractions.familyMorphismRetraction_reduction R f V U W Z h a b d⟩
  let u' : {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber D) ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ D ≫ u = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ D ≫ c'} :=
    ⟨(GroupRetractions.familyMorphismGroupRetraction R f V' W' Z h' (s.trans b) d).val,
      GroupRetractions.familyMorphismRetraction_reduction R f V' U W' Z h' (t.trans a) (s.trans b) d⟩
  have hc : M ≫ c = c' := by
    change M ≫ ((Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X a d).val ≫ F) = _
    rw [← Category.assoc, Family.GroupRetractionRestriction.familyCommonOpenGroupRetraction_restrict]
  have hu : M ≫ u.val = u'.val :=
    RetractionRestriction.familyMorphismGroupRetraction_restrict R f V V' W W' t s h h' d Z b
  exact Constructed.ConormalDeformedSquare.constructedIdentityLiftConormalEquiv_deformed_square ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y) C D q m
    (Dual.TensorMapCoordinates.dualTensorMapCoordinates_reduction n q (Family.RestrictionCoordinates.familyReferenceRestrictionCoordinates_reduction ℂ R X t d))
    (Dual.TensorMapCoordinates.dualTensorMapCoordinates_eps n) c c' u u' hc hu z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.DefectRestriction
