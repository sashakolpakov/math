import OAI.Analysis.HodgeTheory.Decomposition.WeakGlobalSmooth
import OAI.Analysis.HodgeTheory.Decomposition.SmoothWeakEquation

/-! # Smooth Harmonic -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SmoothHarmonic.Constructions

noncomputable section

section

/-! Every element of the actual weak harmonic kernel has a genuine
smooth closed and coclosed representative. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projective_weak_harmonic_is_smooth (u : WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n) :
    ∃ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1),
      SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a = u.val := by
  apply WeakGlobalSmooth.Constructions.projective_weak_solution_is_smooth V n u.val 0
  rw [map_zero]
  exact WeakEquation.Constructions.projectiveWeakHarmonic_is_weak_solution V n u

def projectiveSmoothHarmonic (u : WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) :=
  (projective_weak_harmonic_is_smooth V n u).choose

theorem projectiveSmoothHarmonic_energy (u : WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n) :
    SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n (projectiveSmoothHarmonic V n u) = u.val :=
  (projective_weak_harmonic_is_smooth V n u).choose_spec

theorem projectiveSmoothHarmonic_L2 (u : WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n) :
    Form.Constructions.smoothToProjectiveL2 V (n + 1) (projectiveSmoothHarmonic V n u) =
      WeakHarmonics.Constructions.projectiveWeakHarmonicInclusion V n u :=
  congrArg (EnergyDomain.Constructions.projectiveEnergyInclusion V n) (projectiveSmoothHarmonic_energy V n u)

theorem projectiveSmoothHarmonic_laplacian (u : WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n) :
    AdjointAlgebra.Constructions.projectivePositiveLaplacian V n (projectiveSmoothHarmonic V n u) = 0 := by
  apply (SmoothWeakEquation.Constructions.projective_smooth_weak_equation_iff V n _ 0).mp
  rw [projectiveSmoothHarmonic_energy, map_zero]
  exact WeakEquation.Constructions.projectiveWeakHarmonic_is_weak_solution V n u

theorem projectiveSmoothHarmonic_closed_coclosed (u : WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveSmoothHarmonic V n u) = 0 ∧
      AdjointAlgebra.Constructions.projectiveCodifferential V n (projectiveSmoothHarmonic V n u) = 0 :=
  (AdjointAlgebra.Constructions.projectivePositiveLaplacian_eq_zero_iff V n _).mp (projectiveSmoothHarmonic_laplacian V n u)

theorem projective_smooth_energy_mem_weakHarmonics_iff
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a ∈ WeakHarmonics.Constructions.ProjectiveWeakHarmonics V n ↔ AdjointAlgebra.Constructions.projectivePositiveLaplacian V n a = 0 := by
  constructor
  · intro ha
    apply (SmoothWeakEquation.Constructions.projective_smooth_weak_equation_iff V n a 0).mp
    rw [map_zero]
    exact WeakEquation.Constructions.projectiveWeakHarmonic_is_weak_solution V n ⟨SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a, ha⟩
  · intro ha
    have h := (SmoothWeakEquation.Constructions.projective_smooth_weak_equation_iff V n a 0).mpr ha (SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a)
    rw [map_zero, inner_zero_left] at h
    exact (inner_self_eq_zero.mp h)

end

section

/-! The normalized weak Green solution for a smooth form is smooth and
solves the classical Hodge equation after subtracting its harmonic part. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

def projectiveSmoothHarmonicPart
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) :=
  projectiveSmoothHarmonic V n (WeakHarmonics.Constructions.projectiveWeakHarmonicPart V n (Form.Constructions.smoothToProjectiveL2 V (n + 1) f))

theorem projectiveSmoothHarmonicPart_L2
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    Form.Constructions.smoothToProjectiveL2 V (n + 1) (projectiveSmoothHarmonicPart V n f) =
      WeakHarmonics.Constructions.projectiveWeakHarmonicInclusion V n (WeakHarmonics.Constructions.projectiveWeakHarmonicPart V n (Form.Constructions.smoothToProjectiveL2 V (n + 1) f)) :=
  projectiveSmoothHarmonic_L2 V n _

theorem projectiveSmoothHarmonicPart_closed_coclosed
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveSmoothHarmonicPart V n f) = 0 ∧
      AdjointAlgebra.Constructions.projectiveCodifferential V n (projectiveSmoothHarmonicPart V n f) = 0 :=
  projectiveSmoothHarmonic_closed_coclosed V n _

theorem projective_weak_green_is_smooth
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    ∃ b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1),
      SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n b = WeakEquation.Constructions.projectiveWeakGreenSolution V n (Form.Constructions.smoothToProjectiveL2 V (n + 1) f) := by
  apply WeakGlobalSmooth.Constructions.projective_weak_solution_is_smooth V n _ (f - projectiveSmoothHarmonicPart V n f)
  rw [map_sub, projectiveSmoothHarmonicPart_L2]
  exact WeakEquation.Constructions.projectiveWeakGreen_is_weak_solution V n _

def projectiveSmoothGreen
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1) :=
  (projective_weak_green_is_smooth V n f).choose

theorem projectiveSmoothGreen_energy
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n (projectiveSmoothGreen V n f) =
      WeakEquation.Constructions.projectiveWeakGreenSolution V n (Form.Constructions.smoothToProjectiveL2 V (n + 1) f) :=
  (projective_weak_green_is_smooth V n f).choose_spec

theorem projectiveSmoothGreen_laplacian
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    AdjointAlgebra.Constructions.projectivePositiveLaplacian V n (projectiveSmoothGreen V n f) = f - projectiveSmoothHarmonicPart V n f := by
  apply (SmoothWeakEquation.Constructions.projective_smooth_weak_equation_iff V n _ _).mp
  rw [projectiveSmoothGreen_energy, map_sub, projectiveSmoothHarmonicPart_L2]
  exact WeakEquation.Constructions.projectiveWeakGreen_is_weak_solution V n _

theorem projective_smooth_hodge_decomposition
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    f = projectiveSmoothHarmonicPart V n f +
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AdjointAlgebra.Constructions.projectiveCodifferential V n (projectiveSmoothGreen V n f)) +
        AdjointAlgebra.Constructions.projectiveCodifferential V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveSmoothGreen V n f)) := by
  have h := projectiveSmoothGreen_laplacian V n f
  change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AdjointAlgebra.Constructions.projectiveCodifferential V n (projectiveSmoothGreen V n f)) +
    AdjointAlgebra.Constructions.projectiveCodifferential V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveSmoothGreen V n f)) =
      f - projectiveSmoothHarmonicPart V n f at h
  rw [add_assoc, h]
  abel

end

section

/-! Every closed smooth positive-degree form has a genuine harmonic
representative, with an explicit smooth exact correction from the Green operator. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projective_closed_coexact_green_eq_zero
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hf : DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = 0) :
    AdjointAlgebra.Constructions.projectiveCodifferential V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveSmoothGreen V n f)) = 0 := by
  apply AdjointAlgebra.Constructions.coexact_closed_eq_zero V (n + 1) _ (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveSmoothGreen V n f)) rfl
  have h := congrArg DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projective_smooth_hodge_decomposition V n f)
  rw [map_add, map_add, hf, (projectiveSmoothHarmonicPart_closed_coclosed V n f).1,
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared, zero_add, zero_add] at h
  exact h.symm

theorem projective_closed_harmonic_representative
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hf : DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = 0) :
    f = projectiveSmoothHarmonicPart V n f +
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (AdjointAlgebra.Constructions.projectiveCodifferential V n (projectiveSmoothGreen V n f)) := by
  have h := projective_smooth_hodge_decomposition V n f
  rw [projective_closed_coexact_green_eq_zero V n f hf, add_zero] at h
  exact h

theorem exists_projective_harmonic_representative
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hf : DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = 0) :
    ∃ h : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1),
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d h = 0 ∧ AdjointAlgebra.Constructions.projectiveCodifferential V n h = 0 ∧
        ∃ b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
          f = h + DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b :=
  ⟨projectiveSmoothHarmonicPart V n f, (projectiveSmoothHarmonicPart_closed_coclosed V n f).1,
    (projectiveSmoothHarmonicPart_closed_coclosed V n f).2,
    AdjointAlgebra.Constructions.projectiveCodifferential V n (projectiveSmoothGreen V n f), projective_closed_harmonic_representative V n f hf⟩

theorem projective_harmonic_representative_unique
    (h k : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hδh : AdjointAlgebra.Constructions.projectiveCodifferential V n h = 0) (hδk : AdjointAlgebra.Constructions.projectiveCodifferential V n k = 0)
    (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (hb : h - k = DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) : h = k := by
  apply sub_eq_zero.mp
  apply AdjointAlgebra.Constructions.exact_coclosed_eq_zero V n (h - k) b hb.symm
  rw [map_sub, hδh, hδk, sub_self]

end

/-! The actual positive-degree smooth harmonic space is canonically
isomorphic to the genuine closed/exact de Rham quotient. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

abbrev ProjectiveSmoothHarmonics := (AdjointAlgebra.Constructions.projectivePositiveLaplacian V n).ker

def projectiveHarmonicToClosed : ProjectiveSmoothHarmonics V n →ₗ[ℂ]
    DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (n + 1) :=
  (ProjectiveSmoothHarmonics V n).subtype.codRestrict
    (DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (n + 1))
    (fun a => ((AdjointAlgebra.Constructions.projectivePositiveLaplacian_eq_zero_iff V n a.val).mp a.property).1)

def projectiveHarmonicDeRhamClass : ProjectiveSmoothHarmonics V n →ₗ[ℂ]
    DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient V.analyticModel V.analyticSpace (n + 1) :=
  (DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms V.analyticModel V.analyticSpace (n + 1)).mkQ.comp
    (projectiveHarmonicToClosed V n)

theorem projectiveHarmonicDeRhamClass_injective : Function.Injective (projectiveHarmonicDeRhamClass V n) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro a ha
  have hz : (DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms V.analyticModel V.analyticSpace (n + 1)).mkQ
      (projectiveHarmonicToClosed V n a) = 0 := ha
  have hexact := (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨b, hb⟩ := (DifferentialForms.Manifold.ManifoldDeRham.mem_manifoldExactClosedForms_iff V.analyticModel V.analyticSpace (n + 1) _).mp hexact
  have hδ := ((AdjointAlgebra.Constructions.projectivePositiveLaplacian_eq_zero_iff V n a.val).mp a.property).2
  have hazero := AdjointAlgebra.Constructions.exact_coclosed_eq_zero V n a.val b hb hδ
  exact show a = 0 from Subtype.ext hazero

theorem projectiveHarmonicDeRhamClass_surjective : Function.Surjective (projectiveHarmonicDeRhamClass V n) := by
  intro q
  obtain ⟨f, rfl⟩ := (DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms V.analyticModel V.analyticSpace (n + 1)).mkQ_surjective q
  obtain ⟨h, hd, hδ, b, hfb⟩ := exists_projective_harmonic_representative V n f.val f.property
  let a : ProjectiveSmoothHarmonics V n :=
    ⟨h, (AdjointAlgebra.Constructions.projectivePositiveLaplacian_eq_zero_iff V n h).mpr ⟨hd, hδ⟩⟩
  refine ⟨a, ?_⟩
  change (DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms V.analyticModel V.analyticSpace (n + 1)).mkQ
    (projectiveHarmonicToClosed V n a) =
      (DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms V.analyticModel V.analyticSpace (n + 1)).mkQ f
  apply (sub_eq_zero.mp)
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (DifferentialForms.Manifold.ManifoldDeRham.mem_manifoldExactClosedForms_iff V.analyticModel V.analyticSpace (n + 1) _).mpr
  refine ⟨-b, ?_⟩
  change DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (-b) = h - f.val
  rw [map_neg, hfb]
  abel

def projectiveHarmonicDeRhamEquiv : ProjectiveSmoothHarmonics V n ≃ₗ[ℂ]
    DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient V.analyticModel V.analyticSpace (n + 1) :=
  LinearEquiv.ofBijective (projectiveHarmonicDeRhamClass V n)
    ⟨projectiveHarmonicDeRhamClass_injective V n, projectiveHarmonicDeRhamClass_surjective V n⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.SmoothHarmonic.Constructions
