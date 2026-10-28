import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.GeometricPairing
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneSpanning
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection
import OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology

/-! # Canonical Exterior -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CanonicalExterior.CM.Construction

noncomputable section

/-! Supply the existing exterior-cohomology input on each actual abelian
product used in the switch construction. Its H1 Hodge structure is the
canonical one on the variety's rational cohomology. -/

theorem pureBettiH1_disjoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Disjoint (V.pureBettiSubspace 1 0) (V.pureBettiSubspace 0 1) := by
  apply Submodule.disjoint_def.mpr
  intro c hc hd
  obtain ⟨x, hx, hxc⟩ := hc
  obtain ⟨y, hy, hyc⟩ := hd
  have hxy : x = y := (V.deRhamBettiIso 1).toLinearEquiv.injective (hxc.trans hyc.symm)
  have hz : x = 0 := Submodule.disjoint_def.mp
    (ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.pureDeRham_one_disjoint (E := V.analyticModel) (M := V.analyticSpace))
      x hx (hxy.symm ▸ hy)
  rw [← hxc, hz, map_zero]

theorem complexifiedH1_complementary (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IsCompl
      ((V.pureBettiSubspace 1 0).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1))
      ((V.pureBettiSubspace 0 1).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)) := by
  let e := ComplexOperations.CM.Construction.projectiveComplexification V 1
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hy
    apply e.injective
    rw [map_zero]
    exact Submodule.disjoint_def.mp (pureBettiH1_disjoint V) _ hx hy
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    have hx : e x ∈ V.pureBettiSubspace 1 0 ⊔ V.pureBettiSubspace 0 1 := by
      rw [ComplexMultiplication.HodgeComparison.OneSpanning.CM.Construction.pureBetti_one_sup_top]
      trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    apply Submodule.mem_sup.mpr
    refine ⟨e.symm a, ?_, e.symm b, ?_, ?_⟩
    · change e (e.symm a) ∈ V.pureBettiSubspace 1 0
      simpa only [e.apply_symm_apply] using ha
    · change e (e.symm b) ∈ V.pureBettiSubspace 0 1
      simpa only [e.apply_symm_apply] using hb
    · rw [← map_add, hab, e.symm_apply_apply]

def canonicalH1 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1) where
  finiteDimensional := AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite V 1
  holomorphic := (V.pureBettiSubspace 1 0).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)
  antiholomorphic := (V.pureBettiSubspace 0 1).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)
  complementary := complexifiedH1_complementary V
  conjugate_mem x := by
    constructor
    · intro hx
      have h := ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_antiholomorphic V _ hx
      rw [← GeometricPairing.CM.Construction.canonical_h1_conjugation, ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] at h
      exact h
    · intro hx
      change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
        (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x) ∈ V.pureBettiSubspace 0 1
      rw [GeometricPairing.CM.Construction.canonical_h1_conjugation]
      exact ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_holomorphic V _ hx

def canonicalExterior (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A (canonicalH1 A.variety) :=
  Classical.choice (hexterior A (canonicalH1 A.variety) rfl rfl)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CanonicalExterior.CM.Construction
