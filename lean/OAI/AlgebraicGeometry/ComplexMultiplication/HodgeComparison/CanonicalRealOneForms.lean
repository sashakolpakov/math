import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalOneForms
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation

/-! # Canonical Real One Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalRealOneForms.CM.Construction

noncomputable section

section

/-! Canonical one-form representatives respect complex conjugation.
In particular rational classes have actual real-valued representatives. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

theorem conjugate_holomorphic_closed_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : a ∈ AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 1 0) :
    Conjugation.CM.Construction.conjugateClosedForm a ∈ AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 0 1 := by
  apply (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (p := 0) (q := 1) _).mpr
  exact Conjugation.CM.Construction.conjugateRawForm_holomorphic a.val.val
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (p := 1) (q := 0) _).mp ha)

theorem conjugate_antiholomorphic_closed_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : a ∈ AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 0 1) :
    Conjugation.CM.Construction.conjugateClosedForm a ∈ AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 1 0 := by
  apply (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (p := 1) (q := 0) _).mpr
  exact Conjugation.CM.Construction.conjugateRawForm_antiholomorphic a.val.val
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (p := 0) (q := 1) _).mp ha)

theorem hodgeClosedOne_conjugate_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : a ∈ CanonicalOneForms.CM.Construction.hodgeClosedOneForms V) : Conjugation.CM.Construction.conjugateClosedForm a ∈ CanonicalOneForms.CM.Construction.hodgeClosedOneForms V := by
  obtain ⟨ah, hh, aa, haa, rfl⟩ := Submodule.mem_sup.mp ha
  apply Submodule.mem_sup.mpr
  refine ⟨Conjugation.CM.Construction.conjugateClosedForm aa, conjugate_antiholomorphic_closed_mem V aa haa,
    Conjugation.CM.Construction.conjugateClosedForm ah, conjugate_holomorphic_closed_mem V ah hh, ?_⟩
  exact (add_comm _ _).trans (Conjugation.CM.Construction.conjugateClosedFormMap.map_add ah aa).symm

def canonicalBettiOneRepresentative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.complexCohomology 1 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 :=
  (CanonicalOneForms.CM.Construction.canonicalDeRhamOneRepresentative V).comp (V.deRhamBettiIso 1).inv.hom

theorem canonicalBettiOneRepresentative_class (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.complexCohomology 1) :
    (V.deRhamBettiIso 1).hom (V.deRhamClass 1 (canonicalBettiOneRepresentative V c)) = c := by
  change (V.deRhamBettiIso 1).hom
    (V.deRhamClass 1 (CanonicalOneForms.CM.Construction.canonicalDeRhamOneRepresentative V ((V.deRhamBettiIso 1).inv c))) = c
  rw [CanonicalOneForms.CM.Construction.canonicalDeRhamOneRepresentative_class]
  exact (V.deRhamBettiIso 1).toLinearEquiv.apply_symm_apply c

theorem canonicalBettiOneRepresentative_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.complexCohomology 1) : canonicalBettiOneRepresentative V c ∈ CanonicalOneForms.CM.Construction.hodgeClosedOneForms V :=
  CanonicalOneForms.CM.Construction.canonicalDeRhamOneRepresentative_mem V ((V.deRhamBettiIso 1).inv c)

theorem canonicalBettiOneRepresentative_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.complexCohomology 1) :
    canonicalBettiOneRepresentative V (BettiConjugation.CM.Construction.conjugateBettiH1 V c) =
      Conjugation.CM.Construction.conjugateClosedForm (canonicalBettiOneRepresentative V c) := by
  apply CanonicalOneForms.CM.Construction.hodgeClosedOne_class_injective V _ _ (canonicalBettiOneRepresentative_mem V _)
    (hodgeClosedOne_conjugate_mem V _ (canonicalBettiOneRepresentative_mem V c))
  apply (V.deRhamBettiIso 1).toLinearEquiv.injective
  exact (canonicalBettiOneRepresentative_class V _).trans
    ((congrArg (BettiConjugation.CM.Construction.conjugateBettiH1 V) (canonicalBettiOneRepresentative_class V c)).symm.trans
      (BettiConjugation.CM.Construction.conjugateBettiH1_formClass V (canonicalBettiOneRepresentative V c)))

def canonicalRationalOneRepresentative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.rationalCohomology 1 →ₗ[ℚ]
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj
        (ModuleCat.of ℂ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)) :=
  ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
    (ModuleCat.ofHom (canonicalBettiOneRepresentative V))).hom.comp
      (V.rationalCohomologyInclusion 1).hom

theorem canonicalRationalOneRepresentative_class (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.rationalCohomology 1) :
    (V.deRhamBettiIso 1).hom (V.deRhamClass 1 (canonicalRationalOneRepresentative V c)) =
      V.rationalCohomologyInclusion 1 c :=
  canonicalBettiOneRepresentative_class V (V.rationalCohomologyInclusion 1 c)

theorem canonicalRationalOneRepresentative_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.rationalCohomology 1) :
    Conjugation.CM.Construction.conjugateClosedForm (canonicalRationalOneRepresentative V c) =
      canonicalRationalOneRepresentative V c := by
  have h := canonicalBettiOneRepresentative_conjugate V (V.rationalCohomologyInclusion 1 c)
  have hc : BettiConjugation.CM.Construction.conjugateBettiH1 V (V.rationalCohomologyInclusion 1 c) =
      V.rationalCohomologyInclusion 1 c :=
    PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialH1_rational (Betti.Scheme.schemePointSpace V.toOver) c
  exact h.symm.trans (congrArg (canonicalBettiOneRepresentative V) hc)

theorem canonicalRationalOneRepresentative_im_zero (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.rationalCohomology 1) (x : V.analyticSpace)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, V.analyticModel) x) :
    ((canonicalRationalOneRepresentative V c).val x v).im = 0 := by
  have h := congrArg (fun a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 => a.val x v)
    (canonicalRationalOneRepresentative_conjugate V c)
  have hi := congrArg Complex.im h
  change -((canonicalRationalOneRepresentative V c).val x v).im =
    ((canonicalRationalOneRepresentative V c).val x v).im at hi
  linarith

end

/-! Canonical representatives preserve the actual pure Hodge pieces and
commute with finite complex linear combinations of rational classes. -/

theorem canonicalBettiOneRepresentative_holomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.complexCohomology 1) (hc : c ∈ V.pureBettiSubspace 1 0) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0
      (canonicalBettiOneRepresentative V c).val.val := by
  obtain ⟨a, ha, hclass⟩ := (V.mem_pureBettiSubspace_iff 1 0 c).mp hc
  have hat := (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (p := 1) (q := 0) a.val.val).mpr ha
  have heq : canonicalBettiOneRepresentative V c = a := by
    apply CanonicalOneForms.CM.Construction.hodgeClosedOne_class_injective V _ _ (canonicalBettiOneRepresentative_mem V c)
      (Submodule.mem_sup_left hat)
    apply (V.deRhamBettiIso 1).toLinearEquiv.injective
    exact (canonicalBettiOneRepresentative_class V c).trans hclass.symm
  rw [heq]
  exact hat

theorem canonicalBettiOneRepresentative_antiholomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : V.complexCohomology 1) (hc : c ∈ V.pureBettiSubspace 0 1) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 0 1
      (canonicalBettiOneRepresentative V c).val.val := by
  obtain ⟨a, ha, hclass⟩ := (V.mem_pureBettiSubspace_iff 0 1 c).mp hc
  have hat := (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (p := 0) (q := 1) a.val.val).mpr ha
  have heq : canonicalBettiOneRepresentative V c = a := by
    apply CanonicalOneForms.CM.Construction.hodgeClosedOne_class_injective V _ _ (canonicalBettiOneRepresentative_mem V c)
      (Submodule.mem_sup_right hat)
    apply (V.deRhamBettiIso 1).toLinearEquiv.injective
    exact (canonicalBettiOneRepresentative_class V c).trans hclass.symm
  rw [heq]
  exact hat

theorem canonicalRationalOneRepresentative_complex_combination (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (q : ι → V.rationalCohomology 1) (t : ι → ℂ) :
    (∑ i, t i • (canonicalRationalOneRepresentative V (q i) :
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)) =
    canonicalBettiOneRepresentative V
      (∑ i, t i • (V.rationalCohomologyInclusion 1 (q i) : V.complexCohomology 1)) := by
  let qC : ι → V.complexCohomology 1 := fun i => V.rationalCohomologyInclusion 1 (q i)
  let a : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1 :=
    fun i => canonicalRationalOneRepresentative V (q i)
  change (∑ i, t i • a i) = canonicalBettiOneRepresentative V (∑ i, t i • qC i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (map_smul (canonicalBettiOneRepresentative V) (t i)
    (qC i)).symm

theorem canonicalRational_combination_holomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (q : ι → V.rationalCohomology 1) (t : ι → ℂ)
    (ht : (∑ i, t i • (V.rationalCohomologyInclusion 1 (q i) : V.complexCohomology 1)) ∈
      V.pureBettiSubspace 1 0) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 0
      (∑ i, t i • (canonicalRationalOneRepresentative V (q i) :
        Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)).val.val := by
  rw [canonicalRationalOneRepresentative_complex_combination]
  exact canonicalBettiOneRepresentative_holomorphic V _ ht

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalRealOneForms.CM.Construction
