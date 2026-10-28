import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerFunctionalPositive
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TopAlternating
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealKahlerFunctional

/-! # Kahler Top Trace -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction

noncomputable section

/-! The positive geometric functional on the actual rational top cup
product, with degree transports and the order of the cup factors explicit. -/

theorem singularCohomologyCast_eq_cast {R : Type} [CommRing R] (X : TopCat.{0})
    {n m : ℕ} (h : n = m) (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n) :
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) h a =
      cast (congrArg (fun k => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X k : Type)) h) a := by
  subst m
  rfl

theorem singularCohomologyCast_trans {R : Type} [CommRing R] (X : TopCat.{0})
    {n m p : ℕ} (h : n = m) (h' : m = p) (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n) :
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) h'
      (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) h a) =
      AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj X) (ModuleCat.of R R) (h.trans h') a := by
  subst m p
  rfl

def fubiniStudyTopTrace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    V.complexCohomology (2 + (k + k)) →ₗ[ℂ] ℂ :=
  (KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k).comp
    (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver)) (ModuleCat.of ℂ ℂ) (by omega))

theorem fubiniStudyTopTrace_rational_real (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : V.rationalCohomology (2 + (k + k))) :
    (fubiniStudyTopTrace V k (V.rationalCohomologyInclusion (2 + (k + k)) a)).im = 0 := by
  change (KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k
    (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast _ _ (by omega : 2 + (k + k) = (k + 1) + (k + 1))
      (V.rationalCohomologyInclusion (2 + (k + k)) a))).im = 0
  have hc := singularCohomologyCast_eq_cast (R := ℂ) (Betti.Scheme.schemePointSpace V.toOver)
    (by omega : 2 + (k + k) = (k + 1) + (k + 1))
    (V.rationalCohomologyInclusion (2 + (k + k)) a)
  have h := RationalCupUnit.CM.Construction.rationalToComplexCohomology_cast (Betti.Scheme.schemePointSpace V.toOver)
    (by omega : 2 + (k + k) = (k + 1) + (k + 1)) a
  exact (congrArg (fun t => (KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k t).im) (hc.trans h.symm)).trans
    (RealKahlerFunctional.CM.Construction.fubiniStudyBettiFunctional_rational_real V k _)

theorem projectiveFormBettiClass_smul (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (c : ℂ) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V n (c • a) = c • AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V n a := by
  unfold AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass
  rw [map_smul, map_smul]

theorem topCup_two_swap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : V.complexCohomology 2) (b : V.complexCohomology (k + k)) :
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver)) (ModuleCat.of ℂ ℂ)
      (by omega : (k + k) + 2 = (k + 1) + (k + 1))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) (k + k) 2 b a) =
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver)) (ModuleCat.of ℂ ℂ)
      (by omega : 2 + (k + k) = (k + 1) + (k + 1))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) 2 (k + k) a b) := by
  have h := AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm (Betti.Scheme.schemePointSpace V.toOver) a b
  simp only [pow_mul, neg_one_sq, one_pow, one_smul] at h
  rw [h, singularCohomologyCast_trans]

theorem fubiniStudyMixedTop_bettiClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1) :
    AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V ((k + 1) + (k + 1)) (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a) =
      Complex.I • AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace V.toOver)) (ModuleCat.of ℂ ℂ)
        (by omega : 2 + (k + k) = (k + 1) + (k + 1))
        (TopCup.CM.Construction.complexH1TopCup V k (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 a)
          (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 (Conjugation.CM.Construction.conjugateClosedForm a))) := by
  unfold KahlerProjective.CM.Construction.fubiniStudyMixedTop
  rw [AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_cast, AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_wedge,
    projectiveFormBettiClass_smul, AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_wedge]
  rw [← singularCohomologyCast_eq_cast]
  have hk : AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V (k + k) (Powers.CM.Construction.fubiniStudyPower V k) =
      V.rationalCohomologyInclusion (k + k) (Powers.CM.Construction.fubiniStudyPowerQ V k) := Powers.CM.Construction.fubiniStudyPower_comparison V k
  rw [hk, map_smul, map_smul]
  apply congrArg (fun t : V.complexCohomology ((k + 1) + (k + 1)) => Complex.I • t)
  exact topCup_two_swap V k _ _

theorem fubiniStudyTopTrace_form_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0 a.val.val) (hne : a ≠ 0) :
    0 < (Complex.I * fubiniStudyTopTrace V k
      (TopCup.CM.Construction.complexH1TopCup V k (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 a)
        (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 (Conjugation.CM.Construction.conjugateClosedForm a)))).re := by
  have h := KahlerFunctionalPositive.CM.Construction.fubiniStudyBettiFunctional_mixedTop_pos V k hdim a ha hne
  change 0 < (KahlerCohomologyFunctional.CM.Construction.fubiniStudyBettiFunctional V k
    (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V ((k + 1) + (k + 1)) (KahlerProjective.CM.Construction.fubiniStudyMixedTop V k a))).re at h
  rw [fubiniStudyMixedTop_bettiClass, map_smul, smul_eq_mul] at h
  exact h

theorem fubiniStudyTopTrace_holomorphic_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel)
    (u : V.complexCohomology 1) (hu : u ∈ V.pureBettiSubspace 1 0) (hne : u ≠ 0) :
    0 < (Complex.I * fubiniStudyTopTrace V k
      (TopCup.CM.Construction.complexH1TopCup V k u (BettiConjugation.CM.Construction.conjugateBettiH1 V u))).re := by
  obtain ⟨a, ha, he⟩ := (V.mem_pureBettiSubspace_iff 1 0 u).mp hu
  change AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 a = u at he
  have hna : a ≠ 0 := by
    intro hz
    apply hne
    rw [← he, hz]
    unfold AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass
    rw [map_zero, map_zero]
  have hc := BettiConjugation.CM.Construction.conjugateBettiH1_formClass V a
  change BettiConjugation.CM.Construction.conjugateBettiH1 V (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 a) =
    AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass V 1 (Conjugation.CM.Construction.conjugateClosedForm a) at hc
  have hp := fubiniStudyTopTrace_form_positive V k hdim a
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree a.val.val).mpr ha) hna
  rw [← hc, he] at hp
  exact hp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction
