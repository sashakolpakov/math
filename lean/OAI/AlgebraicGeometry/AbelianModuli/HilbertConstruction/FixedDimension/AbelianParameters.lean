import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GroupGlobalParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GroupConnectedRepresentation

/-! # Abelian Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.AbelianParameters

noncomputable section

/-! The concrete bounded Hilbert group parameter has an actual quasi-projective open carrying a universal projective abelian scheme of the prescribed relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ) (g : ℕ) (Pm Pi : Polynomial ℚ)

instance fixedDimensionHilbertGroupParameter_noetherian :
    IsNoetherian (GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi).left :=
  (GroupGlobalParameter.fixedDimensionHilbertGroupParameterQuasiProjectivePresentation S n P g Pm Pi).noetherian

instance fixedDimensionHilbertGroupUniversalFamily_smooth :
    Smooth (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi).hom := by
  have := GroupParameters.fixedDimensionHilbertGroupUniversalFamily_dimension S n P g Pm Pi
  exact SmoothOfRelativeDimension.smooth g _

local instance fixedHilbertGroupSmooth : Smooth (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi).hom :=
  fixedDimensionHilbertGroupUniversalFamily_smooth S n P g Pm Pi

local instance fixedHilbertGroupBaseNoetherian :
    IsLocallyNoetherian (GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).left :=
  (fixedDimensionHilbertGroupParameter_noetherian S n P g Pm Pi).toIsLocallyNoetherian

local instance fixedHilbertGroupObject : GrpObj (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
  GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj S n P g Pm Pi

local instance fixedHilbertGroupCommutative : IsCommMonObj (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
  GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj_comm S n P g Pm Pi

def fixedDimensionHilbertAbelianParameter : Over S :=
  @Projective.GroupConnectedParameters.projectiveGroupConnectedParameter _ (GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi)
    (fixedHilbertGroupBaseNoetherian S n P g Pm Pi)
    (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
    (fixedDimensionHilbertGroupUniversalFamily_smooth S n P g Pm Pi)
    (fixedHilbertGroupObject S n P g Pm Pi)
    (GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi)

def fixedDimensionHilbertAbelianParameterInclusion :
    fixedDimensionHilbertAbelianParameter S n P g Pm Pi ⟶ GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi :=
  @Projective.GroupConnectedParameters.projectiveGroupConnectedParameterInclusion S (GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi)
    (fixedHilbertGroupBaseNoetherian S n P g Pm Pi)
    (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
    (fixedDimensionHilbertGroupUniversalFamily_smooth S n P g Pm Pi)
    (fixedHilbertGroupObject S n P g Pm Pi)
    (GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi)

instance fixedDimensionHilbertAbelianParameterInclusion_open :
    IsOpenImmersion (fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left :=
  @Projective.GroupConnectedParameters.projectiveGroupConnectedParameterInclusion_open S (GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi)
    (fixedHilbertGroupBaseNoetherian S n P g Pm Pi)
    (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
    (fixedDimensionHilbertGroupUniversalFamily_smooth S n P g Pm Pi)
    (fixedHilbertGroupObject S n P g Pm Pi)
    (GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi)

def fixedDimensionHilbertAbelianParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :=
  @Projective.GroupConnectedParameters.projectiveGroupConnectedParameterQuasiProjectivePresentation S (GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi)
    (fixedHilbertGroupBaseNoetherian S n P g Pm Pi)
    (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
    (fixedDimensionHilbertGroupUniversalFamily_smooth S n P g Pm Pi)
    (fixedHilbertGroupObject S n P g Pm Pi)
    (GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi) inferInstance
    (GroupGlobalParameter.fixedDimensionHilbertGroupParameterQuasiProjectivePresentation S n P g Pm Pi)

def fixedDimensionHilbertUniversalAbelianScheme :
    Abelian.Schemes.AbelianScheme g (fixedDimensionHilbertAbelianParameter S n P g Pm Pi).left :=
  @Projective.GroupConnectedParameters.projectiveGroupConnectedUniversalAbelianScheme S (GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi)
    (fixedHilbertGroupBaseNoetherian S n P g Pm Pi)
    (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
    (fixedDimensionHilbertGroupUniversalFamily_smooth S n P g Pm Pi)
    (fixedHilbertGroupObject S n P g Pm Pi)
    (GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi) g
    (GroupParameters.fixedDimensionHilbertGroupUniversalFamily_dimension S n P g Pm Pi)
    (fixedHilbertGroupCommutative S n P g Pm Pi)

def fixedDimensionHilbertUniversalAbelianProjectivePresentation :
    Projective.ProjectivePresentations.ProjectivePresentation (fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).scheme :=
  @Projective.GroupConnectedFamily.projectiveGroupConnectedPresentation _
    (fixedHilbertGroupBaseNoetherian S n P g Pm Pi)
    (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
    (fixedDimensionHilbertGroupUniversalFamily_smooth S n P g Pm Pi)
    (fixedHilbertGroupObject S n P g Pm Pi)
    (GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi)

def fixedDimensionHilbertAbelianParameterPointEquiv (T : Over S) :
    (T ⟶ fixedDimensionHilbertAbelianParameter S n P g Pm Pi) ≃
      {c : T ⟶ GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi //
        GeometricallyConnected ((Over.pullback c.left).obj
          (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)).hom} :=
  @Projective.GroupConnectedParameters.projectiveGroupConnectedParameterPointEquiv S (GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi)
    (fixedHilbertGroupBaseNoetherian S n P g Pm Pi)
    (GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
    (fixedDimensionHilbertGroupUniversalFamily_smooth S n P g Pm Pi)
    (fixedHilbertGroupObject S n P g Pm Pi)
    (GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi) T

theorem fixedDimensionHilbertAbelianParameter_geometric_family :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation (fixedDimensionHilbertAbelianParameter S n P g Pm Pi)) ∧
    ∃ A : Abelian.Schemes.AbelianScheme g (fixedDimensionHilbertAbelianParameter S n P g Pm Pi).left,
      Nonempty (Projective.ProjectivePresentations.ProjectivePresentation A.scheme) :=
  ⟨⟨fixedDimensionHilbertAbelianParameterQuasiProjectivePresentation S n P g Pm Pi⟩,
    fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi,
    ⟨fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.AbelianParameters
