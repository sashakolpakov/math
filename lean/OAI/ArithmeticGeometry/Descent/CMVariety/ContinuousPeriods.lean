import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodTransversality

/-! # Continuous Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPeriods.Abelian.IntrinsicPeriods

noncomputable section

/-!
Neighborhood rigidity for continuous marked periods of actual abelian
varieties. Transversality is proved on a neighborhood from a continuous
holomorphic frame; it is not included as a neighborhood assumption.

For an arithmetic abelian-scheme family, construction of local integral
markings and of this continuous frame is still a geometric obligation.
No such construction, or moduli representation, is postulated here.
-/

open _root_.CategoryTheory
open scoped _root_.Topology

variable {S ι : Type} [TopologicalSpace S] [Fintype ι]

/-- In a continuously framed marked family, the finite CM enhancement
forces all sufficiently nearby actual abelian varieties to be algebraically
group-isomorphic, respecting the marked native period map. -/
theorem continuous_marked_family_locally_isomorphic
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking ι (A s))
    (H : ∀ s, AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((A s).variety.rationalCohomology 1))
    (hH : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 (A s).variety (H s))
    (d : ℕ) (frame : S → (Fin d → ℂ) →L[ℂ] (ι → ℂ))
    (hframe : ∀ s, (frame s).toLinearMap.range =
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s) (H s)).holomorphic.map MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap)
    (s₀ : S) (hcont : ContinuousAt frame s₀) (hinj : Function.Injective (frame s₀))
    (hCM : (A s₀).HasCMH1) :
    ∃ (r : ℕ) (g : Fin r → ((A s₀).toOver ⟶ (A s₀).toOver)),
      (∀ i, IsMonHom (g i)) ∧
      ∀ k : ∀ s, Fin r → ((A s).toOver ⟶ (A s).toOver),
        (∀ s i, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s₀) (g i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (k s i)) →
        ∀ᶠ s in 𝓝 s₀, MarkedPeriodClassification.Abelian.IntrinsicPeriods.HasMarkedGroupIso (A s₀) (A s) (b s₀) (b s) := by
  obtain ⟨H₀, hH₀, r, g, hg, hrigid⟩ := MarkedRigidity.Abelian.IntrinsicPeriods.hasCMH1_marked_local_rigidity (A s₀) hCM (b s₀)
  have hsame : H s₀ = H₀ := Rigidity.Abelian.weightOne_eq_of_holomorphic_eq _ _
    ((hH s₀).1.trans hH₀.1.symm)
  let W := (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s₀) H₀).antiholomorphic.map MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap
  have hcompl : IsCompl (frame s₀).toLinearMap.range W := by
    rw [hframe s₀, hsame]
    exact (Submodule.orderIsoMapComap MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates).isCompl
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s₀) H₀).complementary
  have hneigh := PeriodTransversality.Abelian.eventually_isCompl_range frame s₀ hcont W hinj hcompl
  refine ⟨r, g, hg, ?_⟩
  intro k hmatrix
  filter_upwards [hneigh] with s hs
  apply hrigid (A s) (b s) (H s) (hH s) (k s) (hmatrix s)
  rw [hframe s] at hs
  exact (Submodule.orderIsoMapComap MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates).isCompl_iff.mpr hs

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ContinuousPeriods.Abelian.IntrinsicPeriods
