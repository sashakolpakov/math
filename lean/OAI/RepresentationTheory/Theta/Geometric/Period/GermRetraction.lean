import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets

/-! # Germ Retraction -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.GermRetraction

noncomputable section

/-! Retraction to any neighborhood preserves the value and derivative at
the base point, and acts on the literal algebra of differentiable functions. -/

open Filter
open scoped _root_.Topology

def periodNeighborhoodRetraction (x : LinearTheta.BallCoordinates) (S : Set LinearTheta.BallCoordinates) :
    LinearTheta.BallCoordinates → LinearTheta.BallCoordinates := by
  classical
  exact fun y => if y ∈ S then y else x

theorem periodNeighborhoodRetraction_local (x : LinearTheta.BallCoordinates) (S : Set LinearTheta.BallCoordinates)
    (hS : S ∈ 𝓝 x) : periodNeighborhoodRetraction x S =ᶠ[𝓝 x] id := by
  filter_upwards [hS] with y hy
  exact ite_eq_left hy

def periodGermRetraction (x : LinearTheta.BallCoordinates) (S : Set LinearTheta.BallCoordinates) (hS : S ∈ 𝓝 x) :
    DifferentialNaturality.functionsAt x →ₐ[ℂ] DifferentialNaturality.functionsAt x where
  toFun f := ⟨f.val ∘ periodNeighborhoodRetraction x S,
    f.property.congr_of_eventuallyEq ((periodNeighborhoodRetraction_local x S hS).fun_comp f.val)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem periodGermRetraction_firstOrder (x u : LinearTheta.BallCoordinates)
    (S : Set LinearTheta.BallCoordinates) (hS : S ∈ 𝓝 x) :
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets.firstOrderEvaluation x u).comp (periodGermRetraction x S hS) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets.firstOrderEvaluation x u := by
  apply AlgHom.ext
  intro f
  exact AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets.firstOrderEvaluation_germ x u _ _
    ((periodNeighborhoodRetraction_local x S hS).fun_comp f.val)

end

end OAI.RepresentationTheory.Theta.Geometric.Period.GermRetraction
