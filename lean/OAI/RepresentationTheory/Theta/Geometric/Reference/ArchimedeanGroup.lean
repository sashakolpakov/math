import OAI.RepresentationTheory.Theta.Geometric.StableCMArithmetic
import OAI.RepresentationTheory.Theta.Geometric.Finite.ActionFree
import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

/-! # Archimedean Group -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The exact finite subgroup has a discrete, free, properly
discontinuous action at the active archimedean place. -/

set_option backward.isDefEq.respectTransparency false

open OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.finiteArithmeticSubgroup : Subgroup D.RationalSU :=
  ((SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup).comap D.rationalFinite

def Data.ActiveHeckeThetaData.archimedeanArithmeticSubgroup : Subgroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU D.pel.reference.b D.pel.reference.μ) :=
  D.finiteArithmeticSubgroup.map (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap D.pel.reference.b D.pel.reference.μ)

variable (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

include hg in
theorem Data.ActiveHeckeThetaData.reference_positive_other_embedding (ν : E →+* ℂ)
    (hν : ν ≠ D.pel.reference.μ) (hνc : ν ≠ (starRingEnd ℂ).comp D.pel.reference.μ) :
    0 < (ν D.pel.reference.b).re := by
  obtain ⟨⟨i, side⟩, hi⟩ := hg.reference_admissible.1.2 ν.toRatAlgHom
  have hpos := hg.reference_admissible.2.2.2.2.1
  cases side
  · have he : (D.pel.reference.embeddings i).toRingHom = ν := congrArg AlgHom.toRingHom hi
    have hne : i ≠ D.pel.reference.distinguished := by
      intro h
      subst i
      exact hν he.symm
    rw [← he]
    exact hpos i hne
  · have he : (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (D.pel.reference.embeddings i)).toRingHom = ν :=
      congrArg AlgHom.toRingHom hi
    have hne : i ≠ D.pel.reference.distinguished := by
      intro h
      subst i
      exact hνc he.symm
    rw [← he]
    simpa [AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding] using hpos i hne

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.finiteArithmetic_le_stable :
    D.finiteArithmeticSubgroup ≤ StableCMArithmetic.stableUnitarySubgroup D.pel.reference.lattice D.pel.reference.b := by
  intro g hg' x
  exact (D.finiteIntegral_preserves_reference_lattice hg hc hgood hdegree g hg' x).symm

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.archimedeanArithmetic_discrete : DiscreteTopology D.archimedeanArithmeticSubgroup := by
  rcases hg.reference_admissible with ⟨_, hb, hb0, _, _, _, hδ0, hδ, _, hL, _⟩
  let H := (StableCMArithmetic.stableUnitarySubgroup D.pel.reference.lattice D.pel.reference.b).map
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap D.pel.reference.b D.pel.reference.μ)
  let : DiscreteTopology H := StableCMArithmetic.stableUnitary_archimedean_discrete D.pel.reference.lattice
    D.pel.reference.b hL hb hb0 D.pel.reference.imaginaryScalar hδ hδ0 D.pel.reference.μ
    (D.reference_positive_other_embedding hg)
  have hle : D.archimedeanArithmeticSubgroup ≤ H :=
    Subgroup.map_mono (D.finiteArithmetic_le_stable hg hc hgood hdegree)
  let f : D.archimedeanArithmeticSubgroup → H := fun g => ⟨g.val, hle g.property⟩
  exact DiscreteTopology.of_continuous_injective
    (f := f) (continuous_subtype_val.subtype_mk _) (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun t : H => t.val) h)

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.archimedeanArithmetic_free : IsCancelSMul D.archimedeanArithmeticSubgroup D.domain := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  obtain ⟨a, ha, he⟩ := g.property
  have hax : D.periodMap a x.val = x.val := by
    rw [Data.ActiveHeckeThetaData.periodMap, Period.Ne.rationalPeriodPerm_on_ball D.pel.reference.b D.pel.reference.μ a x]
    rw [he]
    exact congrArg Subtype.val hx
  have ha1 := D.finiteIntegral_fixedPoint hg hc hgood hdegree a ha x hax
  apply Subtype.ext
  rw [← he, ha1, map_one]
  rfl

include hg hc hgood hdegree in
theorem Data.ActiveHeckeThetaData.archimedeanArithmetic_properlyDiscontinuous :
    ProperlyDiscontinuousSMul D.archimedeanArithmeticSubgroup D.domain := by
  let : DiscreteTopology D.archimedeanArithmeticSubgroup := D.archimedeanArithmetic_discrete hg hc hgood hdegree
  have hb := hg.reference_admissible.2.1
  have him : (D.pel.reference.μ D.pel.reference.b).im = 0 := by
    have he := congrArg D.pel.reference.μ hb
    rw [NumberField.IsCMField.complexEmbedding_complexConj] at he
    exact Complex.conj_eq_iff_im.mp he
  exact Geometry.ComplexBall.ArithmeticQuotientBoostBall.discrete_ballAction_properlyDiscontinuous _ him hg.reference_admissible.2.2.2.1 _

end

end OAI.RepresentationTheory.Theta.Geometric
