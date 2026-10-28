import OAI.AlgebraicGeometry.AbelianVariety.HodgeBasis
import OAI.AlgebraicGeometry.AbelianVariety.CharacterBasis
import OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup

/-! # Hodge Characters -/

namespace OAI.AlgebraicGeometry.AbelianVariety.HodgeCharacters.Constructions.ExteriorCohomology

noncomputable section

open scoped TensorProduct Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
local instance (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) : LinearOrder (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) :=
  linearOrderOfSTO WellOrderingRel

def hodgeExteriorSigns (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (n : ℕ)
    (t : Set.powersetCard (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) n) : Fin n → Bool :=
  fun i => HodgeBasis.Constructions.ExteriorCohomology.hodgeBasisSign H (Set.powersetCard.ofFinEmbEquiv.symm t i)

def hodgeExteriorCharacter (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (n : ℕ)
    (t : Set.powersetCard (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) n) : ℂˣ → ℂ :=
  Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter
    (Fintype.card {i // hodgeExteriorSigns H n t i = true})
    (Fintype.card {i // hodgeExteriorSigns H n t i = false})

theorem hodgeExteriorSigns_sum (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (n : ℕ)
    (t : Set.powersetCard (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) n) :
    (∑ i, ComplexMultiplication.SignSwitch.CM.signValue (hodgeExteriorSigns H n t i)) = ComplexMultiplication.ExteriorTypedBasis.CM.exteriorBasisSignSum n (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasisSign H) t :=
  ComplexMultiplication.ExteriorTypedBasis.CM.sum_orderedExteriorIndex n (fun i => ComplexMultiplication.SignSwitch.CM.signValue (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasisSign H i)) t

theorem hodgeExteriorCharacter_eq_iff (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (p q : ℕ)
    (t : Set.powersetCard (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) (p + q)) :
    hodgeExteriorCharacter H (p + q) t = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q ↔
      ComplexMultiplication.ExteriorTypedBasis.CM.exteriorBasisSignSum (p + q) (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasisSign H) t = (p : ℤ) - q := by
  constructor
  · intro h
    have he := CharacterBasis.Constructions.ExteriorCohomology.bidegreeCharacter_eq_imp_signed_eq
      (Fintype.card {i // hodgeExteriorSigns H (p + q) t i = true})
      (Fintype.card {i // hodgeExteriorSigns H (p + q) t i = false}) p q
      (congrFun h)
    have hs := ComplexMultiplication.SignSwitch.CM.signSum_eq_counts
      (fun i (_ : Unit) => hodgeExteriorSigns H (p + q) t i) ()
    rw [← hodgeExteriorSigns_sum]
    exact hs.trans he
  · intro h
    have hc := (ComplexMultiplication.ExteriorTypedBasis.CM.signTotal_eq_sub_iff_counts p q (hodgeExteriorSigns H (p + q) t)).mp
      ((hodgeExteriorSigns_sum H (p + q) t).trans h)
    unfold hodgeExteriorCharacter
    rw [hc.1, hc.2]

/-- The covector scalar action transported through the actual Betti comparison. -/
def bettiScalarAction (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) (z : ℂˣ) :
    A.variety.complexCohomology n →ₗ[ℂ] A.variety.complexCohomology n :=
  (PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A n).toLinearMap.comp
    ((Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback A.variety.analyticModel n z).comp
      (PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A n).symm.toLinearMap)

theorem pureBetti_iff_scalarAction (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (a : A.variety.complexCohomology (p + q)) :
    a ∈ A.variety.pureBettiSubspace p q ↔
      ∀ z, bettiScalarAction A (p + q) z a = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z • a := by
  let e := PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A (p + q)
  have htype : a ∈ A.variety.pureBettiSubspace p q ↔
      Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel p q (e.symm a) := by
    have h := PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A p q (e.symm a)
    change e (e.symm a) ∈ A.variety.pureBettiSubspace p q ↔
      Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree A.variety.analyticModel p q (e.symm a) at h
    simpa only [e.apply_symm_apply] using h
  rw [htype]
  constructor
  · intro h z
    have he : Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback A.variety.analyticModel (p + q) z (e.symm a) =
        Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z • e.symm a := by
      ext v
      exact h z v
    change e (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback A.variety.analyticModel (p + q) z (e.symm a)) = _
    rw [he, map_smul, e.apply_symm_apply]
  · intro h z v
    have he := congrArg e.symm (h z)
    change e.symm (e (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback A.variety.analyticModel (p + q) z (e.symm a))) =
      e.symm (Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z • a) at he
    rw [e.symm_apply_apply, map_smul] at he
    exact congrArg (fun f : A.variety.analyticModel [⋀^Fin (p + q)]→L[ℝ] ℂ => f v) he

/-- Once the actual cup monomials have their expected characters, the full type equivalence follows. -/
theorem exteriorCup_pure_of_basis_character (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)) (p q : ℕ)
    (hb : ∀ (t : Set.powersetCard (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) (p + q)) (z : ℂˣ),
      bettiScalarAction A (p + q) z
        (ExteriorCohomologyComplexCup.Constructions.complexExteriorCupEquiv A (p + q) (HodgeBasis.Constructions.ExteriorCohomology.hodgeExteriorBasis H (p + q) t)) =
      hodgeExteriorCharacter H (p + q) t z •
        ExteriorCohomologyComplexCup.Constructions.complexExteriorCupEquiv A (p + q) (HodgeBasis.Constructions.ExteriorCohomology.hodgeExteriorBasis H (p + q) t))
    (x : ComplexMultiplication.WeightOne.CM.Complexification (⋀[ℚ]^(p + q) (A.variety.rationalCohomology 1))) :
    ExteriorCohomologyComplexCup.Constructions.complexExteriorCupEquiv A (p + q) x ∈ A.variety.pureBettiSubspace p q ↔
      x ∈ H.exteriorPureSubspace p q := by
  let e := ExteriorCohomologyComplexCup.Constructions.complexExteriorCupEquiv A (p + q)
  let b := HodgeBasis.Constructions.ExteriorCohomology.hodgeExteriorBasis H (p + q)
  let B := b.map e
  have hB : ∀ z t, bettiScalarAction A (p + q) z (B t) =
      hodgeExteriorCharacter H (p + q) t z • B t := fun z t => hb t z
  rw [pureBetti_iff_scalarAction,
    CharacterBasis.Constructions.ExteriorCohomology.eigen_basis_span_iff B (bettiScalarAction A (p + q)) (hodgeExteriorCharacter H (p + q)) hB]
  have hs : {t | hodgeExteriorCharacter H (p + q) t = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q} =
      {t | ComplexMultiplication.ExteriorTypedBasis.CM.exteriorBasisSignSum (p + q) (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasisSign H) t = (p : ℤ) - q} :=
    Set.ext (fun t => hodgeExteriorCharacter_eq_iff H p q t)
  rw [hs, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.exteriorPureSubspace,
    HodgeBasis.Constructions.ExteriorCohomology.exteriorSignedSubspace_eq_hodgeBasisSpan]
  change e x ∈ Submodule.span ℂ ((fun t => e (b t)) '' _) ↔
    x ∈ Submodule.span ℂ (b '' _)
  rw [← Set.image_image]
  let s := b '' {t | ComplexMultiplication.ExteriorTypedBasis.CM.exteriorBasisSignSum (p + q) (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasisSign H) t = (p : ℤ) - q}
  have hmap : Submodule.span ℂ (e '' s) = (Submodule.span ℂ s).map e.toLinearMap :=
    (Submodule.map_span e.toLinearMap s).symm
  change e x ∈ Submodule.span ℂ (e '' s) ↔ x ∈ Submodule.span ℂ s
  rw [hmap]
  constructor
  · rintro ⟨y, hy, he⟩
    exact e.injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianVariety.HodgeCharacters.Constructions.ExteriorCohomology
