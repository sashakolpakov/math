import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalGeneration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedModulePushforwardFaithful
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorMonoidal

/-! # Closed Global Generation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration

noncomputable section

/-! Finite global generators for all sufficiently positive twists on an actual projective closed subscheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedModulePushforwardFaithful
namespace Dimension

universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

local instance closedProjectiveGlobalGenerationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem closedProjective_eventually_hasFiniteGlobalGenerators {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → FiniteGlobalGenerators.HasFiniteGlobalGenerators
      (M ⊗ (Scheme.Modules.pullback f).obj
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)) := by
  let P := (Scheme.Modules.pushforward f).obj M
  have : P.IsQuasicoherent := Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  have : P.IsFiniteType := Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f
  obtain ⟨b, hb⟩ := GlobalGeneration.Dimension.projective_eventually_hasFiniteGlobalGenerators P j
  refine ⟨b, fun n hn => ?_⟩
  let F := Scheme.Modules.pullback f
  let : F.Monoidal := PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let H := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  have hG := (hb n hn).pullback f
  have hTensor : FiniteGlobalGenerators.HasFiniteGlobalGenerators (F.obj P ⊗ F.obj H) :=
    hG.of_iso (Functor.Monoidal.μIso F P H).symm
  let T := (InvertibleTensorEquivalence.invertibleRightTensorEquivalence (F.obj H)
    ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible j n).pullback f)).functor
  have := ClosedModulePushforwardFaithful.closedModulePullback_counit_epi f M
  exact hTensor.of_epi (T.map ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M))

end Dimension

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration
