import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverDegree

/-! # Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cover.CM

noncomputable section

/-! Construct the accepted principal-refinement interface from an actual
algebraic map, holomorphic local sheets, and positive finite fiber degree.
The fundamental-class degree field is proved, never supplied by the caller. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

/-- Degree transport of the canonical integral complex class. -/
def complexFundamentalInDegree
    (d k : ℕ) {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (Fin d → ℂ) X] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 X]
    (h : 2 * d = k) : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of X)).homology k :=
  (eqToHom (congrArg (fun n => (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of X)).homology n) h))
    (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d X)

theorem complex_fundamental_degree_in_degree
    (d e k : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactSpace X] [CompactSpace Y]
    [ChartedSpace (Fin d → ℂ) X] [ChartedSpace (Fin e → ℂ) Y]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 X] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 Y]
    (hd : 2 * d = k) (he : 2 * e = k)
    (f : TopCat.of Y ⟶ TopCat.of X) (degree : ℕ) (hpos : 0 < degree)
    (hdegree : ∀ x : X, Nat.card (f ⁻¹' {x}) = degree)
    (hhol : IsLocalDiffeomorph 𝓘(ℂ, Fin e → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 f) :
    HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) k
      (complexFundamentalInDegree e k he) =
        degree • complexFundamentalInDegree d k hd := by
  have hde : d = e := by omega
  subst e
  subst k
  exact CoverDegree.CM.complex_integral_fundamental_map_degree f degree hpos hdegree hhol

/-- The degree-transport interface is definitionally the accepted surface class. -/
theorem surface_integralClass_eq (S : Cm.ProjectiveSurface) :
    S.integralClass = complexFundamentalInDegree S.variety.complexDimension 4
      (X := S.variety.analyticSpace) (by rw [S.property]) := rfl

theorem surface_integral_degree (S T : Cm.ProjectiveSurface)
    (f : T.variety.toOver ⟶ S.variety.toOver)
    (degree : ℕ) (hpos : 0 < degree)
    (hdegree : ∀ x : S.variety.analyticSpace,
      Nat.card {y : T.variety.analyticSpace //
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) y = x} = degree)
    (hhol : IsLocalDiffeomorph
      (M := T.variety.analyticSpace) (N := S.variety.analyticSpace)
      𝓘(ℂ, T.variety.analyticModel) 𝓘(ℂ, S.variety.analyticModel) 1
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)) 4
      T.integralClass = degree • S.integralClass := by
  exact complex_fundamental_degree_in_degree
    S.variety.complexDimension T.variety.complexDimension 4
    (X := S.variety.analyticSpace) (Y := T.variety.analyticSpace)
    (by rw [S.property]) (by rw [T.property])
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) degree hpos hdegree hhol

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

/-- Construct a refinement from genuine covering data; derive its degree law. -/
def refinementOfHolomorphicCover
    {B : HeckeCycles.GeometricSource.CM.BallDatum K} {N M : ℕ}
    (S : Cm.PrincipalBallSurface K B N) (T : Cm.PrincipalBallSurface K B M)
    (hNM : N ∣ M)
    (f : T.surface.variety.toOver ⟶ S.surface.variety.toOver)
    (hover : ∀ z : B.Domain,
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) (T.projection z) = S.projection z)
    (hcover : IsCoveringMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f))
    (degree : ℕ) (hpos : 0 < degree)
    (hdegree : ∀ x : S.surface.variety.analyticSpace,
      Nat.card {y : T.surface.variety.analyticSpace //
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) y = x} = degree)
    (hhol : IsLocalDiffeomorph
      (M := T.surface.variety.analyticSpace) (N := S.surface.variety.analyticSpace)
      𝓘(ℂ, T.surface.variety.analyticModel) 𝓘(ℂ, S.surface.variety.analyticModel) 1
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)) :
    Cm.PrincipalRefinement K S T where
  divides := hNM
  map := f
  over_ball := hover
  covering := hcover
  degree := degree
  degree_pos := hpos
  fibers := hdegree
  integral_degree := surface_integral_degree S.surface T.surface f degree hpos hdegree hhol

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cover.CM
