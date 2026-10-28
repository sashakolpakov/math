import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaBettiClass
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarFamily
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaLiftKernel

/-! # Theta Class Relations -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaClassRelations.CM

noncomputable section

/-! Full GeometricTheta uniqueness transfers every linear relation of the
original source theta family to its actual Albanese Betti class. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ThetaLiftKernel.Intrinsic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hperiod : D.period = L.period) (hproject : D.project = Theta.Projection.CM.projection E L)
  (hdom : B.domainOpen = D.domain)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness D hg hq hIsogenyQuotient)

include hperiod hproject hdom in
theorem of_family_relation (φ ψ : D.sphericalInputs) (ω : ℂ)
    (h : ScalarFamily.CM.Family.family E L φ.val = ω • ScalarFamily.CM.Family.family E L ψ.val) :
    Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W φ =
      ω • Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W ψ := by
  apply CMExtraction.ThetaLiftKernel.Intrinsic.canonicalTheta_class_relation D hg W.index
    (D.totalPeriodMap W.index W.variety W.component W.cover) W.theta W.canonical W.unique φ ψ ω
  intro x
  have hx : x.val ∈ B.domainOpen := by rw [hdom]; exact x.property
  have hp := congrFun h (⟨x.val, hx⟩ : B.Domain)
  change RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ.val x.val =
    ω • RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) ψ.val x.val at hp
  change RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear D.period D.project φ.val x.val =
    ω • RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear D.period D.project ψ.val x.val
  rw [hperiod, hproject]
  exact hp

include hperiod hproject hdom in
theorem dilation {R : Type*} [AddCommGroup R] [Module ℂ R]
    (J : R →ₗ[ℂ] D.sphericalInputs) (δ : Module.End ℂ R) (ω : ℂ)
    (h : ∀ b, ScalarFamily.CM.Family.family E L (J (δ b)).val =
      ω • ScalarFamily.CM.Family.family E L (J b).val) (b : R) :
    Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W (J (δ b)) =
      ω • Geometric.ThetaBettiClass.CM.classMap D hg hq hIsogenyQuotient W (J b) :=
  of_family_relation E L D hperiod hproject hdom hg hq hIsogenyQuotient W (J (δ b)) (J b) ω (h b)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaClassRelations.CM
