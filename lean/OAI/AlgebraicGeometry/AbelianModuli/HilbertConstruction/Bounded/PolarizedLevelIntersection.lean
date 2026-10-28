import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizationPointCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.LevelIsomorphismParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ParameterIntersections

/-! # Polarized Level Intersection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelIntersection

noncomputable section

/-! A specified closed quasi-projective locus imposes both polarization and full-level preservation on the bounded abelian-isomorphism parameter. Its points are compatible points of the two loci. Identification with complete HilbertConstruction moduli-isomorphism records is a separate step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

def boundedPolarizedLevelIsoParameter : Over S :=
  Closed.ParameterIntersections.closedParameterIntersection (PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P)
    (LevelIsomorphismParameters.boundedFullLevelIsoParameterInclusion A.abelian B.abelian A.level B.level j P)

def boundedPolarizedLevelIsoParameterToPolarization :
    boundedPolarizedLevelIsoParameter A B j P ⟶ PolarizationEqualityParameters.boundedPolarizationIsoParameter A.polarization B.polarization j P :=
  Closed.ParameterIntersections.closedParameterIntersectionFst _ _

def boundedPolarizedLevelIsoParameterToLevel :
    boundedPolarizedLevelIsoParameter A B j P ⟶ LevelIsomorphismParameters.boundedFullLevelIsoParameter A.abelian B.abelian A.level B.level j P :=
  Closed.ParameterIntersections.closedParameterIntersectionSnd _ _

def boundedPolarizedLevelIsoParameterInclusion :
    boundedPolarizedLevelIsoParameter A B j P ⟶ IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P :=
  boundedPolarizedLevelIsoParameterToPolarization A B j P ≫
    PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P

instance boundedPolarizedLevelIsoParameterInclusion_closed :
    IsClosedImmersion (boundedPolarizedLevelIsoParameterInclusion A B j P).left :=
  @IsClosedImmersion.comp _ _ _ _ _ (Closed.ParameterIntersections.closedParameterIntersectionFst_closed _ _)
    (PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion_closed _ _ _ _)

def boundedPolarizedLevelIsoParameterQuasiProjectivePresentation :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (boundedPolarizedLevelIsoParameter A B j P) :=
  (IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A.abelian B.abelian j P).ofClosedImmersion
    (boundedPolarizedLevelIsoParameterInclusion A B j P)

def boundedPolarizedLevelIsoParameterPointEquiv (T : Over S) :
    (T ⟶ boundedPolarizedLevelIsoParameter A B j P) ≃
      {v : (T ⟶ PolarizationEqualityParameters.boundedPolarizationIsoParameter A.polarization B.polarization j P) ×
        (T ⟶ LevelIsomorphismParameters.boundedFullLevelIsoParameter A.abelian B.abelian A.level B.level j P) //
        v.1 ≫ PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P =
          v.2 ≫ LevelIsomorphismParameters.boundedFullLevelIsoParameterInclusion A.abelian B.abelian A.level B.level j P} :=
  Closed.ParameterIntersections.closedParameterIntersectionPointEquiv _ _ T

theorem boundedPolarizedLevelIsoParameter_formallyUnramified :
    FormallyUnramified (boundedPolarizedLevelIsoParameter A B j P).hom := by
  let i := boundedPolarizedLevelIsoParameterInclusion A B j P
  have hi : FormallyUnramified i.left := inferInstance
  have hM := UniversalIso.boundedAbelianIsoParameter_formallyUnramified A.abelian B.abelian j P
  have hc := MorphismProperty.comp_mem (@FormallyUnramified) _ _ hi hM
  exact (congrArg FormallyUnramified i.w).mp hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelIntersection
