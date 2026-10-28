import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.FamilyGroupIntrinsicUniversal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.OperationGroupIsomorphisms

/-! # Group Universal Family Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GroupUniversalFamilyRecovery

noncomputable section

/-! Native points of the represented group parameter recover the pullback
of its universal group family through the actual Cartesian family iso. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance groupRecoveryProductProper {S : Scheme.{u}} (X Y : Over S)
    [IsProper X.hom] [IsProper Y.hom] : IsProper (X ⊗ Y).hom :=
  inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))
local instance groupRecoveryProductSmooth {S : Scheme.{u}} (X Y : Over S)
    [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⊗ Y).hom :=
  inferInstanceAs (Smooth (pullback.fst X.hom Y.hom ≫ X.hom))

variable {S : Scheme.{u}} [IsNoetherian S] {A : Over S} [IsProper A.hom] [Smooth A.hom]
variable {nm ni : ℕ} (jm : (A ⊗ A) ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S nm)
variable (ji : A ⊗ A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S ni)
variable [IsClosedImmersion jm.left] [IsClosedImmersion ji.left] (Pm Pi : Polynomial ℚ)
variable (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation A) {T : Over S}
variable (y : T ⟶ FamilyGroupParameter.boundedFamilyGroupParameter jm ji Pm Pi Q)

def boundedFamilyGroupNativeUniversalFamilyIso :
    (Over.pullback y.left).obj (FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversalFamily jm ji Pm Pi Q) ≅
      (Over.pullback T.hom).obj A :=
  (Single.ParameterBaseChange.singleParameterBaseChangeIso y A).symm

theorem boundedFamilyGroupNativeUniversalFamilyIso_isMonHom :
    letI : GrpObj (FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversalFamily jm ji Pm Pi Q) :=
      FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversalGroupObj jm ji Pm Pi Q
    letI : GrpObj ((Over.pullback T.hom).obj A) :=
      (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T y).val.val.groupObj
      (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T y).property
    IsMonHom (boundedFamilyGroupNativeUniversalFamilyIso jm ji Pm Pi Q y).hom :=
  (FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversal jm ji Pm Pi Q).val.val.geometricBaseChangeIso_isMonHom y
    (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T y).val.val
    (FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversal jm ji Pm Pi Q).property
    (FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv jm ji Pm Pi Q T y).property
    (FamilyGroupIntrinsicUniversal.boundedFamilyGroupNativeUniversal_point jm ji Pm Pi Q y)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GroupUniversalFamilyRecovery
