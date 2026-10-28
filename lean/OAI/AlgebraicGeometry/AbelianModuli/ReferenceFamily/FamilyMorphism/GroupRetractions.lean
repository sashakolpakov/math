import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.ProductCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CommonOpenGroupRetractions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.DualMapReductionSquare

/-! # Group Retractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.GroupRetractions

noncomputable section

section

/-! Pulling the target's original local retraction through the actual
deformed family morphism gives a map to the fixed target group. Its
reduction is the original fixed-fiber family morphism on that chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver FixedFiber.AffineDiagram.fixedFiberTensorDiagram FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ Y) (V : X.left.affineOpens) (W Z : Y.left.affineOpens)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (j : W.1 ≤ Z.1) (d : Derivation ℂ R ℂ)

def familyMorphismGroupRetraction :
    {u : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)) ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y //
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) ≫ u =
        FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X V ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f} := by
  let B := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W)
  let C := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ TangentBasePoint.fixedFamilyFiber ℂ R Y := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ Y W
  have : IsOpenImmersion i.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R ℂ Y W
  let m := ProductCoordinates.familyMorphismProductCoordinates ℂ R f V W h d
  let q := TensorCoordinates.familyMorphismTensorCoordinates R ℂ f V W h
  let a := Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber B) (DualNumber C) (Dual.TensorMapCoordinates.dualTensorMapCoordinates m)
  let r := Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R Y j d
  have hm : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ a = Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B C q ≫ Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B :=
    Affine.DualMapReductionSquare.affineDualMap_reduction_square ℂ B C q (Dual.TensorMapCoordinates.dualTensorMapCoordinates m)
      (Dual.TensorMapCoordinates.dualTensorMapCoordinates_reduction m q (ProductCoordinates.familyMorphismProductCoordinates_reduction ℂ R f V W h d))
  have hr : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ B ≫ r.val = i :=
    r.property.trans (Affine.DualMapReductionSquare.affineChartCoefficientPoint_self ℂ B (TangentBasePoint.fixedFamilyFiber ℂ R Y) i)
  have hi : Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B C q ≫ i = FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X V ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f :=
    TensorCoordinates.familyMorphismTensorCoordinates_inclusion R ℂ f V W h
  refine ⟨a ≫ r.val, ?_⟩
  have hp : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ (a ≫ r.val) = Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B C q ≫ i := by
    rw [← Category.assoc, hm, Category.assoc, hr]
  exact hp.trans hi

theorem familyMorphismGroupRetraction_value :
    (familyMorphismGroupRetraction R f V W Z h j d).val =
      Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R Y W))
        (DualNumber (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V))
        (Dual.TensorMapCoordinates.dualTensorMapCoordinates (ProductCoordinates.familyMorphismProductCoordinates ℂ R f V W h d)) ≫
          (Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R Y j d).val := rfl

end

/-! The actual source retraction followed by the fixed-fiber morphism
and the pulled target retraction have the same original reduction.
Their difference therefore defines a native conormal defect. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver FixedFiber.AffineDiagram.fixedFiberTensorDiagram FixedFiber.AffineDiagram.fixedFiberTensorAlgebras
attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineCoordinateFunctor HilbertConstruction.Affine.CoordinateFunctor.affineCoordinateFunctor HilbertConstruction.AlgebraTensorFunctor.algebraTensorFunctor

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ Y) (V U : X.left.affineOpens) (W Z : Y.left.affineOpens)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (t : V.1 ≤ U.1) (j : W.1 ≤ Z.1) (d : Derivation ℂ R ℂ)

theorem familyMorphismRetraction_reduction :
    Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) ≫
        (familyMorphismGroupRetraction R f V W Z h j d).val =
      Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) ≫
        ((Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X t d).val ≫
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f) := by
  let C := CommAlgCat.of ℂ (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
  let i : EtaleSplittingAt.EtaleSplitting.affineOver ℂ C ⟶ TangentBasePoint.fixedFamilyFiber ℂ R X := FixedFiber.AffineDiagram.fixedFiberTensorInclusion R ℂ X V
  have : IsOpenImmersion i.left := FixedFiber.AffineDiagram.fixedFiberTensorInclusion_open R ℂ X V
  let a := Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X t d
  let b := familyMorphismGroupRetraction R f V W Z h j d
  let F := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f
  have ha : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ a.val = i :=
    a.property.trans (Affine.DualMapReductionSquare.affineChartCoefficientPoint_self ℂ C (TangentBasePoint.fixedFamilyFiber ℂ R X) i)
  exact b.property.trans ((congrArg (fun s => s ≫ F) ha.symm).trans (Category.assoc _ _ _))

variable [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom] [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]

def familyMorphismConormalDefect :
    Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y) →ₗ[ℂ] (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) :=
  Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y) (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
    ((Family.CommonOpenGroupRetractions.familyCommonOpenGroupRetraction R X t d).val ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).map f)
    ⟨(familyMorphismGroupRetraction R f V W Z h j d).val,
      familyMorphismRetraction_reduction R f V U W Z h t j d⟩

def familyMorphismPulledConormalDifference (Z' : Y.left.affineOpens) (j' : W.1 ≤ Z'.1) :
    Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y) →ₗ[ℂ] (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V) :=
  Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y) (ℂ ⊗[R] Family.AffineTangentLifts.familyAffineRing R X V)
    (familyMorphismGroupRetraction R f V W Z' h j' d).val
    ⟨(familyMorphismGroupRetraction R f V W Z h j d).val,
      (familyMorphismGroupRetraction R f V W Z h j d).property.trans
        (familyMorphismGroupRetraction R f V W Z' h j' d).property.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.GroupRetractions
