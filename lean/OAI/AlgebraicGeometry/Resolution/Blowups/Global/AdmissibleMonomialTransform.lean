import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.CenterIncidence
import OAI.AlgebraicGeometry.Resolution.Blowups.PrimeCenterBoundaryIncidence
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialTransform

/-! # Admissible Monomial Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

section

/-! Every integral global center has one intrinsic set of containing boundary labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.divided_iff_contains_integral_center
    [IsIntegral I.subscheme] (i : A.indices) (hproper : I.ideal (A.opens i) ≠ ⊤) (j : β) :
    j ∈ A.divided i ↔ D j ≤ I := by
  let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  let : (I.ideal (A.opens i)).IsPrime := Integral.CenterIncidence.Construction.integral_center_affine_ideal_prime I (A.opens i) hproper
  obtain ⟨C⟩ := A.center i ⟨I.ideal (A.opens i), inferInstance⟩ le_rfl
  rw [C.divided_iff_mem_prime_center (I.ideal (A.opens i)) le_rfl j]
  constructor
  · intro hw
    apply Integral.CenterIncidence.Construction.integral_center_contains_of_affine_containment I (D j) (A.opens i) hproper
    rw [A.component i j]
    apply Ideal.span_le.mpr
    rintro x rfl
    exact hw
  · intro hD
    have h := hD (A.opens i)
    rw [A.component i j] at h
    exact h (Ideal.subset_span (Set.mem_singleton (A.equations i j)))

def AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels [Fintype β] (I : X.IdealSheafData) (D : β → X.IdealSheafData) : Finset β := by
  classical
  exact Finset.univ.filter (fun j => D j ≤ I)

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.divided_eq_integralCenterBoundaryLabels
    [IsIntegral I.subscheme] [Fintype β] (i : A.indices) (hproper : I.ideal (A.opens i) ≠ ⊤) :
    A.divided i = AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D := by
  classical
  ext j
  simp only [AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  exact A.divided_iff_contains_integral_center i hproper j

def CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.uniformIncidence [IsIntegral I.subscheme] [Fintype β] :
    CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D where
  indices := A.indices
  opens := A.opens
  cover := A.cover
  equations := A.equations
  component := A.component
  divided := fun _ => AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D
  contained i j hj := by
    by_cases hproper : I.ideal (A.opens i) ≠ ⊤
    · apply A.contained i j
      rwa [A.divided_eq_integralCenterBoundaryLabels i hproper]
    · rw [not_not.mp hproper]
      trivial
  boundary := A.boundary
  center i := by
    let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
    by_cases hproper : I.ideal (A.opens i) ≠ ⊤
    · rw [← A.divided_eq_integralCenterBoundaryLabels i hproper]
      exact A.center i
    · intro p hp
      exact (p.isPrime.ne_top (top_le_iff.mp ((not_not.mp hproper) ▸ hp))).elim

end

/-! Permissibility alone gives the exact monomial transform for a boundary-compatible integral center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem AdmissibleMonomialTransform.Construction.global_canonical_boundary_permissible_monomial_transform_on_chart
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I M : X.IdealSheafData) (hI : I ≠ ⊥) {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (F : Finset β) (a : β → ℕ) (b : ℕ)
    (hperm : M ≤ I ^ b) (U : X.affineOpens)
    (w : β → Γ(X, U)) (hD : ∀ j, (D j).ideal U = Ideal.span {w j})
    (hM : M.ideal U = Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a})
    (hw : ∀ j ∈ F, w j ∈ I.ideal U) (d : I.ideal U)
    [Algebra ℂ Γ(X, U)]
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) d))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal U) d F w hw)) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI b).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) =
      (MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a b F)).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) := by
  classical
  have hp : Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} ≤ I.ideal U ^ b := by
    rw [← hM]
    exact hperm U
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, hM, MixedBoundary.Construction.boundaryMonomialSheaf_comap_open]
  simp_rw [CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_comap_reesChart I hI D F U w hD hw d hboundary]
  rw [MixedBoundary.Construction.boundaryMonomialSheaf_affineQuotientKernel]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
    (Boundary.MonomialTransform.Construction.boundaryMonomialElement_controlledTransform_of_boundary (.of Γ(X, U))
      (I.ideal U) d F w hw a b hp hboundary)

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.monomial_transform_integral_center
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData} [IsIntegral I.subscheme]
    {β : Type} [Fintype β] {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (hI : I ≠ ⊥) (a : β → ℕ) (b : ℕ) (hperm : MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ b) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (MixedBoundary.Construction.boundaryMonomialSheaf D a) hI b =
      MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a b (AdmissibleMonomialTransform.Construction.integralCenterBoundaryLabels I D)) := by
  let B := A.uniformIncidence
  let Q := B.reesCover hI
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ Q.openCover
  intro p
  let : Algebra ℂ Γ(X, B.opens p.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (B.opens p.1)
  exact AdmissibleMonomialTransform.Construction.global_canonical_boundary_permissible_monomial_transform_on_chart I
    (MixedBoundary.Construction.boundaryMonomialSheaf D a) hI D (B.divided p.1) a b hperm (B.opens p.1)
    (B.equations p.1) (B.component p.1)
    (MixedBoundary.Construction.boundaryMonomialSheaf_local_equations D a (B.opens p.1) (B.equations p.1) (B.component p.1))
    (B.contained p.1) p.2
    (MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, B.opens p.1))
      (I.ideal (B.opens p.1)) (B.equations p.1) (B.divided p.1) (B.contained p.1)
      (B.boundary p.1) (B.center p.1) p.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
