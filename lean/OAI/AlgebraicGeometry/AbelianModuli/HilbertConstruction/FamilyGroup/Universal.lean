import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.CommutativeGroupParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Universal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Universal

noncomputable section

/-! Smoothness, fixed relative dimension, and geometric connectedness pass to the actual universal group family; for such an input family the group-law locus carries a bundled abelian scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left]
variable {X : Over M.left} [IsProper X.hom] [Flat X.hom] (D : Operations.FamilyGroupOperations X)

def familyCommutativeGroupUniversalFamily : Over (Family.CommutativeGroupParameter.familyCommutativeGroupParameter M D).left :=
  (Over.pullback (Family.CommutativeGroupParameter.familyCommutativeGroupParameterInclusion M D).left).obj X

instance familyCommutativeGroupUniversalFamily_proper :
    IsProper (familyCommutativeGroupUniversalFamily M D).hom :=
  inferInstanceAs (IsProper (pullback.snd X.hom (Family.CommutativeGroupParameter.familyCommutativeGroupParameterInclusion M D).left))

instance familyCommutativeGroupUniversalFamily_flat :
    Flat (familyCommutativeGroupUniversalFamily M D).hom :=
  inferInstanceAs (Flat (pullback.snd X.hom (Family.CommutativeGroupParameter.familyCommutativeGroupParameterInclusion M D).left))

instance familyCommutativeGroupUniversalFamily_smooth [Smooth X.hom] :
    Smooth (familyCommutativeGroupUniversalFamily M D).hom :=
  inferInstanceAs (Smooth (pullback.snd X.hom (Family.CommutativeGroupParameter.familyCommutativeGroupParameterInclusion M D).left))

instance familyCommutativeGroupUniversalFamily_connected [GeometricallyConnected X.hom] :
    GeometricallyConnected (familyCommutativeGroupUniversalFamily M D).hom :=
  inferInstanceAs (GeometricallyConnected (pullback.snd X.hom (Family.CommutativeGroupParameter.familyCommutativeGroupParameterInclusion M D).left))

theorem familyCommutativeGroupUniversalFamily_smoothDimension (g : ℕ) [SmoothOfRelativeDimension g X.hom] :
    SmoothOfRelativeDimension g (familyCommutativeGroupUniversalFamily M D).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
    (IsPullback.of_hasPullback X.hom (Family.CommutativeGroupParameter.familyCommutativeGroupParameterInclusion M D).left) inferInstance

def familyGroupLawAbelianScheme (g : ℕ) [SmoothOfRelativeDimension g X.hom]
    [GeometricallyConnected X.hom] : Abelian.Schemes.AbelianScheme g (Family.CommutativeGroupParameter.familyCommutativeGroupParameter M D).left where
  scheme := familyCommutativeGroupUniversalFamily M D
  group := Family.CommutativeGroupParameter.familyCommutativeGroupUniversalGroupObj M D
  commutative := Family.CommutativeGroupParameter.familyCommutativeGroupUniversalGroupObj_comm M D
  proper := inferInstance
  smoothDimension := familyCommutativeGroupUniversalFamily_smoothDimension M D g
  connected := inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Universal
