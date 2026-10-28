import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ResidualUpdate

/-! # Uniform Incidence Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Exact boundary factor updates require constant boundary incidence, without requiring the center to be integral. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.withUniformIncidence
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (F : Finset β) (hF : ∀ i, I.ideal (A.opens i) ≠ ⊤ → A.divided i = F) :
    CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D where
  indices := A.indices
  opens := A.opens
  cover := A.cover
  equations := A.equations
  component := A.component
  divided := fun _ => F
  contained i j hj := by
    by_cases hproper : I.ideal (A.opens i) ≠ ⊤
    · apply A.contained i j
      rwa [hF i hproper]
    · rw [not_not.mp hproper]
      trivial
  boundary := A.boundary
  center i := by
    let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
    by_cases hproper : I.ideal (A.opens i) ≠ ⊤
    · rw [← hF i hproper]
      exact A.center i
    · intro p hp
      exact (p.isPrime.ne_top (top_le_iff.mp ((not_not.mp hproper) ▸ hp))).elim

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.monomial_transform_uniform_incidence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} [Fintype β] {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (F : Finset β) (hF : ∀ i, I.ideal (A.opens i) ≠ ⊤ → A.divided i = F)
    (hI : I ≠ ⊥) (a : β → ℕ) (b : ℕ) (hperm : MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ b) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (MixedBoundary.Construction.boundaryMonomialSheaf D a) hI b =
      MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a b F) := by
  let B := A.withUniformIncidence F hF
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (B.reesCover hI).openCover
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

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.residual_boundary_factor_uniform_incidence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} [Fintype β] {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (F : Finset β) (hF : ∀ i, I.ideal (A.opens i) ≠ ⊤ → A.divided i = F)
    (hI : I ≠ ⊥) (a : β → ℕ) (m b : ℕ) (hperm : MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ (b - m)) :
    CompanionTransform.Construction.globalResidualBoundaryFactorTransform I (MixedBoundary.Construction.boundaryMonomialSheaf D a) hI m b =
      MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents F a m b) := by
  let B := A.withUniformIncidence F hF
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (B.reesCover hI).openCover
  intro p
  let : Algebra ℂ Γ(X, B.opens p.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (B.opens p.1)
  exact GlobalBoundary.ResidualUpdate.Construction.global_boundary_residual_factor_on_chart I (MixedBoundary.Construction.boundaryMonomialSheaf D a) hI D
    (B.divided p.1) a m b hperm (B.opens p.1) (B.equations p.1) (B.component p.1)
    (MixedBoundary.Construction.boundaryMonomialSheaf_local_equations D a (B.opens p.1) (B.equations p.1) (B.component p.1))
    (B.contained p.1) p.2
    (MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, B.opens p.1))
      (I.ideal (B.opens p.1)) (B.equations p.1) (B.divided p.1) (B.contained p.1)
      (B.boundary p.1) (B.center p.1) p.2)

theorem CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.residual_product_uniform_incidence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} [Fintype β] {D : β → X.IdealSheafData} (A : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (F : Finset β) (hF : ∀ i, I.ideal (A.opens i) ≠ ⊤ → A.divided i = F)
    (J : X.IdealSheafData) (hI : I ≠ ⊥) (a : β → ℕ) (m b : ℕ)
    (hM : MixedBoundary.Construction.boundaryMonomialSheaf D a ≤ I ^ (b - m)) (hJ : J ≤ I ^ m) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (MixedBoundary.Construction.boundaryMonomialSheaf D a * J) hI b =
      MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (ResidualBoundaryMonomialUpdate.Construction.residualBoundaryMonomialExponents F a m b) * GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m := by
  rw [CompanionTransform.Construction.globalBlowup_residual_product_transform I (MixedBoundary.Construction.boundaryMonomialSheaf D a) J hI m b hM hJ,
    A.residual_boundary_factor_uniform_incidence F hF hI a m b hM]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
