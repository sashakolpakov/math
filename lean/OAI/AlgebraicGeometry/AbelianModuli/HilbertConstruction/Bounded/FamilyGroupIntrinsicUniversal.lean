import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupRepresentation

/-! # Family Group Intrinsic Universal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupIntrinsicUniversal

noncomputable section

/-! The representing bounded group parameter carries a native universal commutative group on the pullback of the original family, and a bundled abelian scheme when that family has fixed smooth dimension and geometrically connected fibers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance nativeUniversalProductProper {S : Scheme.{u}} (X Y : Over S) [IsProper X.hom] [IsProper Y.hom] :
    IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))

local instance nativeUniversalProductSmooth {S : Scheme.{u}} (X Y : Over S) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)
variable (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A)

def boundedFamilyGroupNativeUniversal :
    FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations jm ji Pm Pi (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q) :=
  FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q _ (𝟙 _)

def boundedFamilyGroupNativeUniversalFamily : Over (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q).left :=
  (Over.pullback (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q).hom).obj A

@[instance_reducible] def boundedFamilyGroupNativeUniversalGroupObj :
    GrpObj (boundedFamilyGroupNativeUniversalFamily jm ji Pm Pi Q) :=
  (boundedFamilyGroupNativeUniversal jm ji Pm Pi Q).val.val.groupObj
    (boundedFamilyGroupNativeUniversal jm ji Pm Pi Q).property

theorem boundedFamilyGroupNativeUniversalGroupObj_comm :
    letI := boundedFamilyGroupNativeUniversalGroupObj jm ji Pm Pi Q
    IsCommMonObj (boundedFamilyGroupNativeUniversalFamily jm ji Pm Pi Q) :=
  (boundedFamilyGroupNativeUniversal jm ji Pm Pi Q).val.val.groupObj_comm
    (boundedFamilyGroupNativeUniversal jm ji Pm Pi Q).property

theorem boundedFamilyGroupNativeUniversal_point {T : Over S}
    (y : T ⟶ FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q) :
    (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T y).val.val =
      (boundedFamilyGroupNativeUniversal jm ji Pm Pi Q).val.val.geometricBaseChange y := by
  have h := ConcreteCategory.congr_hom (CC := fun X : Type u => X)
    ((FamilyGroupRepresentation.boundedFamilyGroupClassifyingIso jm ji Pm Pi Q).hom.naturality y.op)
    (𝟙 (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q))
  change FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T (y ≫ 𝟙 _) =
    (FamilyGroupRepresentation.boundedFamilyGroupFunctor jm ji Pm Pi).map y.op (boundedFamilyGroupNativeUniversal jm ji Pm Pi Q) at h
  rw [Category.comp_id] at h
  exact congrArg (fun D : FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations jm ji Pm Pi T => D.val.val) h

def boundedFamilyGroupNativeUniversalAbelianScheme (g : ℕ)
    [SmoothOfRelativeDimension g A.hom] [GeometricallyConnected A.hom] :
    Abelian.Schemes.AbelianScheme g (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q).left where
  scheme := boundedFamilyGroupNativeUniversalFamily jm ji Pm Pi Q
  group := boundedFamilyGroupNativeUniversalGroupObj jm ji Pm Pi Q
  commutative := boundedFamilyGroupNativeUniversalGroupObj_comm jm ji Pm Pi Q
  proper := inferInstanceAs (IsProper (pullback.snd A.hom (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q).hom))
  smoothDimension := (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
    (IsPullback.of_hasPullback A.hom (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q).hom) inferInstance
  connected := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom (FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q).hom))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupIntrinsicUniversal
