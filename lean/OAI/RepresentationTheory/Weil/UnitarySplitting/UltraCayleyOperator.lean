import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleySynthesisPairing
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianNonzero

/-! # Ultra Cayley Operator -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyOperator.Construction

noncomputable section

/-! The weak Cayley Gaussian is represented by a nonzero linear operator
on the actual nonarchimedean Bruhat space. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

theorem testPairing_ext
    {F : Type} [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (f k : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (h : ∀ u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      ⟪Weak.Construction.testToL2 F d u, Weak.Construction.testToL2 F d f⟫_ℂ = ⟪Weak.Construction.testToL2 F d u, Weak.Construction.testToL2 F d k⟫_ℂ) : f = k := by
  apply Weak.Construction.testToL2_injective F d
  have hh : ⟪Weak.Construction.testToL2 F d (f - k), Weak.Construction.testToL2 F d (f - k)⟫_ℂ = 0 := by
    rw [map_sub, inner_sub_right, ← map_sub, h (f - k), sub_self]
  have hz := inner_self_eq_zero.mp hh
  simpa only [map_sub, sub_eq_zero] using hz

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [IsUltrametricDist F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
variable (g : FrameTransport.Construction.StandardSymplectic F d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
variable (hD : ∀ x, D x = g.val x - x)

include hF hc hu hn hD in
theorem ultraCayley_representable (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ∃ k : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d, ∀ h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      ⟪Weak.Construction.testToL2 F d h, Weak.Construction.testToL2 F d k⟫_ℂ =
        WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
          (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D) f.val h.val := by
  let u := LocalTest.Construction.ultraTestVector F hF d
  obtain ⟨r, hr, hres⟩ := WeylResolutionOperator.Construction.ultraResolution_positive_scalar hF ψ hc hu hn ν u
    (LocalTest.Construction.ultraTestVector_ne_zero F hF d)
  exact ⟨(r : ℂ)⁻¹ • CayleySynthesisPairing.Construction.ultraCayleySynthesis hF ψ hc hu hn ν g D hD u f,
    CayleySynthesisPairing.Construction.ultraCayleySynthesis_normalized_pairing hF ψ hc hu hn ν g D hD u r hr.ne' hres f⟩

def ultraCayleyVector (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d :=
  Classical.choose (ultraCayley_representable hF ψ hc hu hn ν g D hD f)

theorem ultraCayleyVector_pairing (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d h, Weak.Construction.testToL2 F d (ultraCayleyVector hF ψ hc hu hn ν g D hD f)⟫_ℂ =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D) f.val h.val :=
  Classical.choose_spec (ultraCayley_representable hF ψ hc hu hn ν g D hD f) h

def ultraCayleyOperator : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d where
  toFun := ultraCayleyVector hF ψ hc hu hn ν g D hD
  map_add' f k := by
    apply testPairing_ext
    intro h
    rw [ultraCayleyVector_pairing, map_add, inner_add_right,
      ultraCayleyVector_pairing, ultraCayleyVector_pairing]
    exact WeakGaussianLinearity.Construction.weakWeylGaussian_add_left hF ψ hc hu ν hn _
      (CayleySynthesisPairing.Construction.standardCayleyWeylPhase_continuous hF D) f k h
  map_smul' z f := by
    apply testPairing_ext
    intro h
    rw [ultraCayleyVector_pairing, map_smul, inner_smul_right, ultraCayleyVector_pairing]
    exact WeakGaussianLinearity.Construction.weakWeylGaussian_smul_left hF ψ hc hu ν _ z f h

theorem ultraCayleyOperator_pairing (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d h, Weak.Construction.testToL2 F d (ultraCayleyOperator hF ψ hc hu hn ν g D hD f)⟫_ℂ =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D) f.val h.val :=
  ultraCayleyVector_pairing hF ψ hc hu hn ν g D hD f h

theorem ultraCayleyOperator_ne_zero : ultraCayleyOperator hF ψ hc hu hn ν g D hD ≠ 0 := by
  obtain ⟨f, h, hne⟩ := WeakGaussianNonzero.Construction.weakWeylGaussian_nonzero_ultra hF ψ hc hu hn ν _
    (CayleySynthesisPairing.Construction.standardCayleyWeylPhase_continuous hF D)
  intro hz
  apply hne
  rw [← ultraCayleyOperator_pairing hF ψ hc hu hn ν g D hD, hz]
  simp only [LinearMap.zero_apply, map_zero, inner_zero_right]

theorem ultraCayleyOperator_intertwines (w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ultraCayleyOperator hF ψ hc hu hn ν g D hD (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g.val w) (ultraCayleyOperator hF ψ hc hu hn ν g D hD f) := by
  apply testPairing_ext
  intro h
  rw [ultraCayleyOperator_pairing, WeakCayleyCoefficients.Construction.weakCayleyGaussian_intertwines hF ψ hc hu ν g D hD,
    ← ultraCayleyOperator_pairing hF ψ hc hu hn ν g D hD]
  exact (Weyl.Construction.heisenbergOperator_adjoint hF ψ hc hu (g.val w)
    (ultraCayleyOperator hF ψ hc hu hn ν g D hD f) h).symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyOperator.Construction
