import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelIntersection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationProperties

/-! # Polarized Level Universal Conditions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelUniversalConditions

noncomputable section

/-! The intersection's universal bounded isomorphism satisfies the polarization equation and preserves the full level on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ)

theorem boundedPolarizedLevel_universal_polarization :
    (Over.pullback (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P).left).map
        (PolarizationEqualityParameters.boundedPolarizationLeft A.polarization j P) =
      (Over.pullback (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P).left).map
        (PolarizationEqualityParameters.boundedPolarizationRight B.polarization j P) :=
  (PolarizationEqualityParameters.boundedPolarizationIsoParameterPointEquiv A.polarization B.polarization j P _
    (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterToPolarization A B j P)).property

theorem boundedPolarizedLevel_universal_level :
    Level.PreservationProperties.FullLevelPreservesPullback
      (A.level.pullback (IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P).hom)
      (B.level.pullback (IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P).hom)
      (UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom
      (PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P).left := by
  let M := IsoParameters.boundedAbelianIsoParameter A.abelian B.abelian j P
  let W := PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P
  let v := PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterToLevel A B j P
  let i := PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P
  let c := v ≫ LevelIsomorphismParameters.boundedFullLevelIsoParameterInclusion A.abelian B.abelian A.level B.level j P
  have hi : i = c := Closed.ParameterIntersections.closedParameterIntersection_condition _ _
  have hM : IsNoetherian M.left :=
    (IsoParameters.boundedAbelianIsoParameterQuasiProjectivePresentation A.abelian B.abelian j P).noetherian
  have H := Level.PreservationProperties.fullLevelParameter_factor_preserves M (A.abelian.pullback M.hom) (B.abelian.pullback M.hom)
    (A.level.pullback M.hom) (B.level.pullback M.hom)
    (UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom v
  exact (congrArg (fun d : W ⟶ M => Level.PreservationProperties.FullLevelPreservesPullback
    (A.level.pullback M.hom) (B.level.pullback M.hom)
    (UniversalIso.boundedAbelianUniversalIso A.abelian B.abelian j P).hom d.left) hi.symm).mp H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelUniversalConditions
