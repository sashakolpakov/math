import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction

/-! # Twist Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.TwistCoordinates

noncomputable section

/-! A chosen open frame of a line bundle identifies twisting with the
identity functor after restriction, naturally for every module map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
universe u
local instance c44OpenTwistCoordinatesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def openTwistCoordinate {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    tensorRight L ⋙ Scheme.Modules.restrictFunctor U.ι ≅ Scheme.Modules.restrictFunctor U.ι := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let : (Scheme.Modules.pullback U.ι).Monoidal := SheafCohomology.Projective.PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal U.ι
  let : F.Monoidal := Functor.Monoidal.transport (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  exact (Functor.Monoidal.commTensorRight L (F := F)).symm ≪≫
    Functor.isoWhiskerLeft F ((tensoringRight U.toScheme.Modules).mapIso
      (e ≪≫ (SheafCohomology.Projective.TensorSections.monoidalUnitObjIso U.toScheme).symm)) ≪≫
    Functor.isoWhiskerLeft F (rightUnitorNatIso U.toScheme.Modules)

theorem openTwistCoordinate_naturality {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) {M N : X.Modules} (q : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map (q ▷ L) ≫ (openTwistCoordinate L U e).hom.app N =
      (openTwistCoordinate L U e).hom.app M ≫ (Scheme.Modules.restrictFunctor U.ι).map q :=
  (openTwistCoordinate L U e).hom.naturality q

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.TwistCoordinates
