import OAI.ArithmeticGeometry.Descent.CMVariety.Canonical
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedActions
import OAI.ArithmeticGeometry.Descent.CMVariety.EquivariantRigidity
import OAI.ArithmeticGeometry.Descent.CMVariety.IntegralMarkedMaps

/-! # Period Matrix Rigidity -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.PeriodMatrixRigidity.Abelian.IntrinsicPeriods

noncomputable section

/-!
Local rigidity expressed in actual marked period matrices. Both the
canonical Hodge structures and their continuous frames are constructed,
so neither is an input to this theorem. For an arithmetic abelian scheme,
one still has to construct local integral markings and continuous native
tangent coordinates, with locally constant endomorphism matrices.
-/

open _root_.CategoryTheory
open scoped _root_.Topology

variable {S Index : Type} [TopologicalSpace S] [Fintype Index]

/-- Continuous actual period matrices give neighborhood rigidity for
the constructed finite CM enhancement. -/
theorem continuous_period_matrix_locally_equivariant
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (d : ℕ) (e : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s) ≃ₗ[ℂ] (Fin d → ℂ))
    (s₀ : S)
    (hperiod : ContinuousAt
      (fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) s₀)
    (hCM : (A s₀).HasCMH1) :
    ∃ (r : ℕ) (g : Fin r → ((A s₀).toOver ⟶ (A s₀).toOver)),
      (∀ i, IsMonHom (g i)) ∧
      ∀ k : ∀ s, Fin r → ((A s).toOver ⟶ (A s).toOver),
        (∀ s i, IsMonHom (k s i)) →
        (∀ s i, MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s₀) (g i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (k s i)) →
        ∀ᶠ s in 𝓝 s₀,
          EquivariantRigidity.Abelian.IntrinsicPeriods.HasMarkedEquivariantIso (A s₀) (A s) (b s₀) (b s) g (k s) := by
  let p := fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap
  apply EquivariantRigidity.Abelian.IntrinsicPeriods.continuous_marked_family_locally_equivariant A b (fun s => Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s))
    (fun s => Canonical.Abelian.IntrinsicPeriods.canonicalH1_isCanonical (A s)) d (fun s => MarkedActions.Abelian.IntrinsicPeriods.periodTranspose (p s))
    (fun s => MarkedActions.Abelian.IntrinsicPeriods.periodTranspose_range_markedHodge (b s) (e s) (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s))
      (Canonical.Abelian.IntrinsicPeriods.canonicalH1_isCanonical (A s))) s₀
  · exact MarkedActions.Abelian.IntrinsicPeriods.continuous_periodTranspose.continuousAt.comp hperiod
  · apply MarkedActions.Abelian.IntrinsicPeriods.periodTranspose_injective
    exact (e s₀).surjective.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap_surjective (b s₀))
  · exact hCM

theorem continuous_period_and_endomorphism_matrices_locally_rigid
    (A : S → AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (b : ∀ s, MarkedAbelianPeriods.IntrinsicPeriods.Marking Index (A s))
    (d : ℕ) (e : ∀ s, AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel (A s) ≃ₗ[ℂ] (Fin d → ℂ))
    (s₀ : S)
    (hperiod : ContinuousAt
      (fun s => ((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap) s₀)
    (hCM : (A s₀).HasCMH1) :
    ∃ (r : ℕ) (g : Fin r → ((A s₀).toOver ⟶ (A s₀).toOver)),
      (∀ i, IsMonHom (g i)) ∧
      ∀ k : ∀ s, Fin r → ((A s).toOver ⟶ (A s).toOver),
        (∀ s i, IsMonHom (k s i)) →
        (∀ i, k s₀ i = g i) →
        (∀ l i j, ContinuousAt
          (fun s => (MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (k s l)
            ((Pi.basisFun ℚ Index) i) j : ℝ)) s₀) →
        ∀ᶠ s in 𝓝 s₀,
          EquivariantRigidity.Abelian.IntrinsicPeriods.HasMarkedEquivariantIso (A s₀) (A s) (b s₀) (b s) g (k s) := by
  obtain ⟨HA, hHA, r, g, hg, hrigid⟩ :=
    EquivariantRigidity.Abelian.IntrinsicPeriods.hasCMH1_marked_equivariant_rigidity (A s₀) hCM (b s₀)
  have hsame : Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s₀) = HA := Rigidity.Abelian.weightOne_eq_of_holomorphic_eq _ _
    ((Canonical.Abelian.IntrinsicPeriods.canonicalH1_isCanonical (A s₀)).1.trans hHA.1.symm)
  let frame := fun s => MarkedActions.Abelian.IntrinsicPeriods.periodTranspose
    (((e s).toLinearMap.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap (b s))).toContinuousLinearMap)
  have hframe (s : S) : (frame s).toLinearMap.range =
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s) (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s))).holomorphic.map
        MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap :=
    MarkedActions.Abelian.IntrinsicPeriods.periodTranspose_range_markedHodge (b s) (e s) (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s))
      (Canonical.Abelian.IntrinsicPeriods.canonicalH1_isCanonical (A s))
  let W := (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s₀) HA).antiholomorphic.map MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates.toLinearMap
  have hcompl : IsCompl (frame s₀).toLinearMap.range W := by
    rw [hframe s₀, hsame]
    exact (Submodule.orderIsoMapComap MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates).isCompl
      (MarkedPeriodClassification.Abelian.IntrinsicPeriods.markedHodgeStructure (b s₀) HA).complementary
  have hcont : ContinuousAt frame s₀ :=
    MarkedActions.Abelian.IntrinsicPeriods.continuous_periodTranspose.continuousAt.comp hperiod
  have hinj : Function.Injective (frame s₀) := MarkedActions.Abelian.IntrinsicPeriods.periodTranspose_injective _
    ((e s₀).surjective.comp (MarkedAbelianPeriods.IntrinsicPeriods.periodMap_surjective (b s₀)))
  have hneigh := PeriodTransversality.Abelian.eventually_isCompl_range frame s₀ hcont W hinj hcompl
  refine ⟨r, g, hg, ?_⟩
  intro k hk hk₀ hmatrix
  have hconstant : ∀ᶠ s in 𝓝 s₀, ∀ i,
      MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s) (k s i) = MarkedActions.Abelian.IntrinsicPeriods.markedEndomorphism (b s₀) (g i) := by
    rw [Filter.eventually_all]
    intro i
    have h := IntegralMarkedMaps.Abelian.IntrinsicPeriods.markedEndomorphism_eventually_eq_of_continuous A b (fun s => k s i)
      (fun s => hk s i) s₀ (hmatrix i)
    simpa only [hk₀ i] using h
  filter_upwards [hneigh, hconstant] with s hs hsk
  apply hrigid (A s) (b s) (Canonical.Abelian.IntrinsicPeriods.canonicalH1 (A s)) (Canonical.Abelian.IntrinsicPeriods.canonicalH1_isCanonical (A s))
    (k s) (hk s) (fun i => (hsk i).symm)
  rw [hframe s] at hs
  exact (Submodule.orderIsoMapComap MarkedPeriodClassification.Abelian.IntrinsicPeriods.scalarCoordinates).isCompl_iff.mpr hs

end

end OAI.ArithmeticGeometry.Descent.CMVariety.PeriodMatrixRigidity.Abelian.IntrinsicPeriods
