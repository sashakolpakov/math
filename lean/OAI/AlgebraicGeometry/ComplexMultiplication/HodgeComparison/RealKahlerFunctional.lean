import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerCohomologyFunctional
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveBettiConjugation
import OAI.Analysis.DifferentialForms.Manifold.ClassRepresentatives

/-! # Real Kahler Functional -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealKahlerFunctional.CM.Construction

noncomputable section

/-! The constructed Kähler functional commutes with actual Betti
conjugation and takes real values on genuine rational cohomology. -/

open _root_.CategoryTheory

theorem fubiniStudyBettiFunctional_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : V.complexCohomology ((k + 1) + (k + 1))) :
    KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k (PositiveBettiConjugation.CM.Construction.conjugateBettiHSucc V ((k + 1) + k) a) =
      star (KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k a) := by
  have hs : Function.Surjective (fun f : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace
      ((k + 1) + (k + 1)) =>
        (V.deRhamBettiIso ((k + 1) + (k + 1))).hom (V.deRhamClass ((k + 1) + (k + 1)) f)) :=
    (V.deRhamBettiIso ((k + 1) + (k + 1))).toLinearEquiv.surjective.comp
      (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_surjective V.analyticModel V.analyticSpace ((k + 1) + (k + 1)))
  obtain ⟨f, rfl⟩ := hs a
  have hconj := PositiveBettiConjugation.CM.Construction.conjugateBettiHSucc_formClass V ((k + 1) + k) f
  have hclass := KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional_formClass V k f
  have hclassConj := KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional_formClass V k (Conjugation.CM.Construction.conjugateClosedForm f)
  have h := AdjointConjugation.CM.Construction.projectiveL2Pair_conjugate V ((k + 1) + (k + 1)) (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val f.val
  have hreal : Conjugation.CM.Construction.conjugateSmoothForm (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val =
      (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val := congrArg Subtype.val (Powers.CM.Construction.fubiniStudyPower_conjugate V (k + 1))
  rw [hreal] at h
  exact (congrArg (KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k) hconj).trans
    (hclassConj.trans (h.trans (congrArg (star : ℂ → ℂ) hclass).symm))

theorem fubiniStudyBettiFunctional_rational_real (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : V.rationalCohomology ((k + 1) + (k + 1))) :
    (KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k
      (V.rationalCohomologyInclusion ((k + 1) + (k + 1)) a)).im = 0 := by
  have h := fubiniStudyBettiFunctional_conjugate V k
    (V.rationalCohomologyInclusion ((k + 1) + (k + 1)) a)
  have hr : PositiveBettiConjugation.CM.Construction.conjugateBettiHSucc V ((k + 1) + k)
      (V.rationalCohomologyInclusion ((k + 1) + (k + 1)) a) =
      V.rationalCohomologyInclusion ((k + 1) + (k + 1)) a :=
    PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialHSucc_rational (Betti.Scheme.schemePointSpace V.toOver) ((k + 1) + k) a
  rw [hr] at h
  exact Complex.conj_eq_iff_im.mp h.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealKahlerFunctional.CM.Construction
