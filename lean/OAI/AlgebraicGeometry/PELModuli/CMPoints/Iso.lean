import OAI.AlgebraicGeometry.PELModuli.CMPoints.Transport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveRationalBettiIso

/-! # Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Iso

noncomputable section

/-! CM H1 is invariant under actual algebraic scheme isomorphisms.
The comparison uses the original singular-cohomology pullbacks and
their proved preservation of pure Betti type. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions

theorem h1Pullback_iso_holomorphic {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (e : B.toOver ≅ A.toOver)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    (ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback e.hom).baseChange ℂ x ∈ B.h1Holomorphic ↔
      x ∈ A.h1Holomorphic := by
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace B.toOver) 1
    ((ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback e.hom).baseChange ℂ x) ∈ B.variety.pureBettiSubspace 1 0 ↔ _
  have hn : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace B.toOver) 1
      ((ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback e.hom).baseChange ℂ x) =
        Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback e.hom 1
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1 x) :=
    HodgeConjecture.DegreeTwo.Transport.Constructions.complexification_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom) 1 x
  rw [hn]
  exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace_iff e 1 0 _

theorem h1Pullback_iso_antiholomorphic {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (e : B.toOver ≅ A.toOver)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)) :
    (ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback e.hom).baseChange ℂ x ∈ B.h1Antiholomorphic ↔
      x ∈ A.h1Antiholomorphic := by
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace B.toOver) 1
    ((ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback e.hom).baseChange ℂ x) ∈ B.variety.pureBettiSubspace 0 1 ↔ _
  have hn : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace B.toOver) 1
      ((ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback e.hom).baseChange ℂ x) =
        Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback e.hom 1
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1 x) :=
    HodgeConjecture.DegreeTwo.Transport.Constructions.complexification_pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom) 1 x
  rw [hn]
  exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace_iff e 0 1 _

theorem hasCMH1_of_iso {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (e : B.toOver ≅ A.toOver)
    (hA : A.HasCMH1) : B.HasCMH1 := by
  obtain ⟨H, hh, ha, ⟨D⟩⟩ := hA
  let ec : A.variety.rationalCohomology 1 ≃ₗ[ℚ] B.variety.rationalCohomology 1 :=
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiEquiv e 1
  have he : ec.toLinearMap = ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback e.hom := rfl
  refine ⟨H.transport ec, ?_, ?_, ⟨Transport.cmDecompositionTransport D ec⟩⟩
  · ext x
    obtain ⟨y, rfl⟩ := (ec.baseChange ℚ ℂ _ _).surjective x
    rw [ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.transport_holomorphic, hh]
    change y ∈ A.h1Holomorphic ↔ ec.toLinearMap.baseChange ℂ y ∈ B.h1Holomorphic
    rw [he]
    exact (h1Pullback_iso_holomorphic e y).symm
  · ext x
    obtain ⟨y, rfl⟩ := (ec.baseChange ℚ ℂ _ _).surjective x
    rw [ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.transport_antiholomorphic, ha]
    change y ∈ A.h1Antiholomorphic ↔ ec.toLinearMap.baseChange ℂ y ∈ B.h1Antiholomorphic
    rw [he]
    exact (h1Pullback_iso_antiholomorphic e y).symm

theorem hasCMH1_iso_iff {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (e : A.toOver ≅ B.toOver) :
    A.HasCMH1 ↔ B.HasCMH1 :=
  ⟨hasCMH1_of_iso e.symm, hasCMH1_of_iso e⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Iso
