import OAI.RepresentationTheory.Weil.UnitarySplitting.PositiveCommutation

/-! # Normalized Operator Families -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormalizedOperatorFamilies.Construction

noncomputable section

/-! Positive normalization preserves local constancy on every test
vector, as does taking the inverse of the resulting linear equivalence. -/

open Filter _root_.Topology

theorem equiv_inverse_family_locallyConstant
    {P X : Type} [TopologicalSpace P] (A : P → X ≃ X)
    (hA : ∀ x : X, IsLocallyConstant (fun p : P => A p x)) (x : X) :
    IsLocallyConstant (fun p : P => (A p).symm x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  filter_upwards [(hA ((A p).symm x)).eventually_eq p] with t ht
  apply (A t).injective
  rw [(A t).apply_symm_apply, ht, (A p).apply_symm_apply]

variable {F P : Type} [NormedField F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}

theorem positive_operator_radius_eq
    (M : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (A : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hu : u ≠ 0) (r : ℝ) (hr : 0 < r)
    (hM : M u = (r : ℂ) • A u) :
    r = ‖Weak.Construction.testToL2 F d (M u)‖ / ‖Weak.Construction.testToL2 F d u‖ := by
  have hnA : ‖Weak.Construction.testToL2 F d (A u)‖ = ‖Weak.Construction.testToL2 F d u‖ := by
    rw [Weak.Construction.testToL2_norm, Weak.Construction.testToL2_norm, hA]
  rw [hM, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hnA]
  exact (mul_div_cancel_right₀ r (norm_ne_zero_iff.mpr (WeylResolutionOperator.Construction.testToL2_ne_zero u hu))).symm

theorem positive_operator_family_locallyConstant [TopologicalSpace P]
    (M : P → Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (A : P → Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ p f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A p f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hu : u ≠ 0)
    (r : P → ℝ) (hr : ∀ p, 0 < r p)
    (hM : ∀ p f, M p f = (r p : ℂ) • A p f)
    (hc : ∀ f, IsLocallyConstant (fun p : P => M p f)) :
    IsLocallyConstant r ∧ (∀ f, IsLocallyConstant (fun p : P => A p f)) ∧
      ∀ f, IsLocallyConstant (fun p : P => (A p).symm f) := by
  have hre : r = fun p => ‖Weak.Construction.testToL2 F d (M p u)‖ / ‖Weak.Construction.testToL2 F d u‖ := by
    funext p
    exact positive_operator_radius_eq (M p) (A p) (hA p) u hu (r p) (hr p) (hM p u)
  have hrc : IsLocallyConstant r := by
    rw [hre]
    exact (hc u).comp (fun f => ‖Weak.Construction.testToL2 F d f‖ / ‖Weak.Construction.testToL2 F d u‖)
  have hac (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : IsLocallyConstant (fun p : P => A p f) := by
    have heq : (fun p : P => A p f) = fun p => (r p : ℂ)⁻¹ • M p f := by
      funext p
      rw [hM, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hr p).ne'), one_smul]
    rw [heq]
    exact (hrc.prodMk (hc f)).comp (fun z : ℝ × Local.FunctionsMetaplectic.Construction.schwartzBruhat F d => (z.1 : ℂ)⁻¹ • z.2)
  refine ⟨hrc, hac, fun f => ?_⟩
  exact equiv_inverse_family_locallyConstant (fun p => (A p).toEquiv) hac f

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormalizedOperatorFamilies.Construction
