import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupGlobalParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompositeParameterPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.ConnectednessFieldTests

/-! # Group Point Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupPointData

noncomputable section

/-! Global points of the bounded Hilbert group parameter classify a Hilbert parameter point and actual bounded commutative-group operations on its pulled-back family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)

def FixedDimensionHilbertGroupData (T : Over S) :=
  Σ c : T ⟶ Parameters.fixedDimensionHilbertParameter S n P g,
    Bounded.FamilyGroupPointClassification.BoundedCommutativeFamilyGroupOperations
      (GroupParameters.fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
      (GroupParameters.fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi (Over.mk c.left)

def fixedDimensionHilbertGroupPointEquiv (T : Over S) :
    (T ⟶ GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) ≃
      FixedDimensionHilbertGroupData S n P g Pm Pi T :=
  (CompositeParameterPoints.compositeParameterPointEquiv (Parameters.fixedDimensionHilbertParameter S n P g)
    (GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi) T).trans
      (Equiv.sigmaCongrRight (fun c => Bounded.FamilyGroupPointClassification.boundedFamilyGroupParameterNativeEquiv
        (GroupParameters.fixedDimensionHilbertMultiplicationPresentation S n P g).embedding
        (GroupParameters.fixedDimensionHilbertInversionPresentation S n P g).embedding Pm Pi
        (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).quasiProjective (Over.mk c.left)))

def FixedDimensionHilbertGroupData.family {T : Over S}
    (D : FixedDimensionHilbertGroupData S n P g Pm Pi T) : Over T.left :=
  (Over.pullback D.1.left).obj (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme

@[instance_reducible] def FixedDimensionHilbertGroupData.groupObj {T : Over S}
    (D : FixedDimensionHilbertGroupData S n P g Pm Pi T) : GrpObj (D.family S n P g Pm Pi) :=
  D.2.val.val.groupObj D.2.property

omit [AlgebraicGeometry.IsNoetherian S] in
theorem FixedDimensionHilbertGroupData.groupObj_comm {T : Over S}
    (D : FixedDimensionHilbertGroupData S n P g Pm Pi T) :
    letI := D.groupObj S n P g Pm Pi
    IsCommMonObj (D.family S n P g Pm Pi) :=
  D.2.val.val.groupObj_comm D.2.property

def FixedDimensionHilbertGroupData.projective {T : Over S}
    (D : FixedDimensionHilbertGroupData S n P g Pm Pi T) : Projective.ProjectivePresentations.ProjectivePresentation (D.family S n P g Pm Pi) :=
  (Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).baseChange D.1.left

omit [AlgebraicGeometry.IsNoetherian S] in
theorem FixedDimensionHilbertGroupData.dimension {T : Over S}
    (D : FixedDimensionHilbertGroupData S n P g Pm Pi T) :
    SmoothOfRelativeDimension g (D.family S n P g Pm Pi).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
    (IsPullback.of_hasPullback (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme.hom D.1.left)
    (Parameters.fixedDimensionHilbertUniversalFamily_dimension S n P g)

theorem fixedDimensionHilbertGroupPoint_connected_iff (T : Over S)
    (y : T ⟶ GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) :
    GeometricallyConnected (pullback.snd (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi).hom y.left) ↔
      GeometricallyConnected ((fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).family S n P g Pm Pi).hom :=
  Geometric.ConnectednessFieldTests.geometricallyConnected_iterated_pullback_iff
    (Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme.hom
    (GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom y.left

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupPointData
