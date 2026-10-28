import Lean.LibrarySuggestions.Basic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveLevel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Principal
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarCalibration
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAwayFixed
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralOpen

/-! # Projective Away Fixed -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveAwayFixed

noncomputable section

/-! The original descended nonzero theta form removes the projective
character on its full away principal level. The active neighborhood,
rational principal membership and scalar calibration are constructed
from the actual source and marked PEL lattice. -/

attribute [local instance 2000] Subgroup.toGroup Prod.instGroup
open scoped Classical _root_.NumberField _root_.Matrix _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAwayFixed.TestTransport
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators.Local
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalFactorProjection.CM

namespace CM

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false

private theorem scalar_of_mul {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {S T U : V ≃ₗ[F] V} (v : V) (c : F) (h : S = T * U)
    (ht : T v = v) (hu : U v = c • v) : S v = c • v := by
  rw [h, LinearEquiv.mul_apply, hu, map_smul, ht]

private def restrictLeft {A B G : Type*} [Group A] [Group B] [Group G]
    (f : A × B →* G) : A →* G := f.comp (MonoidHom.inl A B)

private def restrictRight {A B G : Type*} [Group A] [Group B] [Group G]
    (f : A × B →* G) : B →* G := f.comp (MonoidHom.inr A B)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance projectiveAwayGroup : Group (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  Subgroup.toGroup (FactorTheta.CM.RationalWeilFactorization.Away E L f)
local instance projectiveAwayMonoid : Monoid (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (projectiveAwayGroup E L f).toMonoid
local instance projectiveAwayMulOneClass : MulOneClass (FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (projectiveAwayGroup E L f).toMulOneClass
local instance projectiveSourceMulOneClass :
    MulOneClass (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f) :=
  (show Group (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × FactorTheta.CM.RationalWeilFactorization.Away E L f)
    from Prod.instGroup).toMulOneClass

def pelProduct :=
  (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb).toMonoidHom.comp
    (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f)

theorem pelProduct_continuous : Continuous (pelProduct E L P hb f) :=
  (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb).continuous.comp
    (IntrinsicActiveClosure.CM.Intrinsic.continuous E L f)

theorem pelProduct_pair (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (a : FactorTheta.CM.RationalWeilFactorization.Away E L f) : pelProduct E L P hb f (u, a) =
      pelProduct E L P hb f (u, 1) * pelProduct E L P hb f (1, a) := by
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using
    map_mul (pelProduct E L P hb f) (u, 1) (1, a)

private theorem action_pair (u : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q])
    (a : FactorTheta.CM.RationalWeilFactorization.Away E L f) : FactorTheta.CM.action E L f (u, a) =
      FactorTheta.CM.action E L f (u, 1) * FactorTheta.CM.action E L f (1, a) := by
  simpa only [mul_one, one_mul] using FactorTheta.CM.action_mul E L f u 1 1 a

theorem pelProduct_away (a : FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    pelProduct E L P hb f (1, a) = MarkedAwayLevel.CM.map E L P hb f a := by
  have result := congrArg (PELFiniteGroup.CM.pel E
    (OppositeCoordinates.CM.coordinates E L.coordinates) P hb)
    (MarkedAwayLevel.CM.assemble_away E L f a)
  exact result

private theorem theta_input_ne_zero (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (hne : ∃ z ∈ B.domain, ∃ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ ≠ 0) :
    Theta.Weil.CM.finiteWeilInput φ ≠ 0 := by
  intro hz
  obtain ⟨z, _hzin, ξ, hvalue⟩ := hne
  let F := RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
  have he := congrArg (fun ψ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) => F ψ z ξ) hz
  have hzero : F 0 z ξ = 0 := congrArg (fun t => t z ξ) (map_zero F)
  exact hvalue ((Theta.Projection.CM.canonical_oneForm_eq_source E L φ z ξ).symm.trans
    (he.trans hzero))

variable {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ P.lattice]
  (b : Module.Basis J ℤ P.lattice) (N : ℕ) (hN : 0 < N)

def activeLevel : OpenSubgroup (Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :=
  ((CMExtraction.PEL.PrincipalOpen.Approximation.pelPrincipalOpenSubgroup E P b N hN).comap
    (restrictLeft (pelProduct E L P hb f))
    ((pelProduct_continuous E L P hb f).comp (continuous_id.prodMk continuous_const))) ⊓
      CMExtraction.IntegralOpen.Intrinsic.integralSL3Open q

theorem rational_principal (hL : P.lattice = B.lattice)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (ha : FactorTheta.CM.RationalWeilFactorization.away E L f g ∈ MarkedAwayLevel.CM.level E L P hb f b N hN)
    (hu : RationalFactorProjection.CM.activeLocal E f g ∈ activeLevel E L P hb f b N hN) :
    B.principalLevel N (Matrix.SpecialLinearGroup.toLin' g.val) := by
  apply Rational.Principal.CM.source_principal E
    (OppositeCoordinates.CM.coordinates E L.coordinates) P hb b hL N hN g
  have he : PELFiniteGroup.CM.pel E
      (OppositeCoordinates.CM.coordinates E L.coordinates) P hb
      (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g) =
      pelProduct E L P hb f (RationalFactorProjection.CM.activeLocal E f g, 1) * pelProduct E L P hb f (1, FactorTheta.CM.RationalWeilFactorization.away E L f g) := by
    exact (congrArg (PELFiniteGroup.CM.pel E
      (OppositeCoordinates.CM.coordinates E L.coordinates) P hb)
      (IntrinsicActiveClosure.CM.Intrinsic.rational E L f g)).symm.trans
        (pelProduct_pair E L P hb f (RationalFactorProjection.CM.activeLocal E f g) (FactorTheta.CM.RationalWeilFactorization.away E L f g))
  have hu' : pelProduct E L P hb f (RationalFactorProjection.CM.activeLocal E f g, 1) ∈ P.adelicPrincipalLevel N := hu.1
  have ha' : pelProduct E L P hb f (1, FactorTheta.CM.RationalWeilFactorization.away E L f g) ∈ P.adelicPrincipalLevel N :=
    (congrArg (fun t : P.FiniteSpecialUnitary => t ∈ P.adelicPrincipalLevel N)
      (pelProduct_away E L P hb f (FactorTheta.CM.RationalWeilFactorization.away E L f g))).mpr ha
  exact (congrArg (fun t : P.FiniteSpecialUnitary => t ∈ P.adelicPrincipalLevel N) he).mpr
    ((P.adelicPrincipalLevel N).mul_mem hu' ha')

theorem fixed (hL : P.lattice = B.lattice)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (hK : P.adelicPrincipalLevel N ≤
      (ProjectiveLevel.CM.level E L P hb (Theta.Weil.CM.finiteWeilInput φ)).toSubgroup)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace)
    (hπ : B.IsBallCover N X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω)
    (hne : ∃ z ∈ B.domain, ∃ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ ≠ 0)
    (hactive : ∀ u ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q,
      FactorTheta.CM.action E L f (u, 1) (Theta.Weil.CM.finiteWeilInput φ) =
        Theta.Weil.CM.finiteWeilInput φ) :
    ∀ a ∈ MarkedAwayLevel.CM.level E L P hb f b N hN,
      FactorTheta.CM.action E L f (1, a) (Theta.Weil.CM.finiteWeilInput φ) =
        Theta.Weil.CM.finiteWeilInput φ := by
  let ψ := Theta.Weil.CM.finiteWeilInput φ
  have hψ : ψ ≠ 0 := theta_input_ne_zero E L φ hne
  let ρ := restrictRight (FactorTheta.CM.action E L f)
  have hline : ∀ a ∈ MarkedAwayLevel.CM.level E L P hb f b N hN,
      ∃ c : ℂˣ, ρ a ψ = (c : ℂ) • ψ :=
    ProjectiveLevel.CM.away_line E L P hb f b N hN ψ hK
  have hfixed (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
      (ha : FactorTheta.CM.RationalWeilFactorization.away E L f g ∈ MarkedAwayLevel.CM.level E L P hb f b N hN)
      (hu : RationalFactorProjection.CM.activeLocal E f g ∈ activeLevel E L P hb f b N hN) :
      ρ (FactorTheta.CM.RationalWeilFactorization.away E L f g) ψ = ψ := by
    let c : ℂˣ := Classical.choose (hline (FactorTheta.CM.RationalWeilFactorization.away E L f g) ha)
    have hc : ρ (FactorTheta.CM.RationalWeilFactorization.away E L f g) ψ = (c : ℂ) • ψ :=
      Classical.choose_spec (hline (FactorTheta.CM.RationalWeilFactorization.away E L f g) ha)
    have hs : WeilData.CM.finiteAction E L g ψ = (c : ℂ) • ψ :=
      (FactorTheta.CM.rational_action E L f g ψ).symm.trans
        (scalar_of_mul ψ (c : ℂ)
          (action_pair E L f (RationalFactorProjection.CM.activeLocal E f g) (FactorTheta.CM.RationalWeilFactorization.away E L f g)) (hactive _ hu.2) hc)
    have hc1 := ScalarCalibration.CM.scalar_one E L φ X N π hπ ω hω hne g
      (rational_principal E L P hb f b N hN hL g ha hu) c hs
    exact hc.trans ((congrArg (fun z : ℂ => z • ψ) hc1).trans (one_smul ℂ ψ))
  exact CMExtraction.DenseAwayFixed.TestTransport.dense_away_level_fixed (RationalAwayTopology.CM.rational E L f)
    (RationalDensity.CM.dense E L f)
    (RationalAwayTopology.CM.away_surjective E L f)
    (CMExtraction.Commutators.Local.sl3_commutator_eq_top (K := Padic q))
    (MarkedAwayLevel.CM.level E L P hb f b N hN) ρ ψ hψ hline
    (activeLevel E L P hb f b N hN) hfixed

--
--
--
end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveAwayFixed
