import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.ChosenGlobalReesCover
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.DifferentialBound

/-! # Canonical Boundary Atlas -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryAtlas.Construction

noncomputable section

/-! Global boundary preservation with an independent incidence set on each affine center chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

structure GlobalMixedCenterAtlas {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (I : X.IdealSheafData) {β : Type} (D : β → X.IdealSheafData) where
  indices : Type
  opens : indices → X.affineOpens
  cover : ⨆ i, (opens i).1 = ⊤
  equations : ∀ i, β → Γ(X, opens i)
  component : ∀ i j, (D j).ideal (opens i) = Ideal.span {equations i j}
  divided : indices → Finset β
  contained : ∀ i j, j ∈ divided i → equations i j ∈ I.ideal (opens i)
  boundary : ∀ i, letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (opens i)
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of Γ(X, opens i)) (equations i)
  center : ∀ i, letI := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (opens i)
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts ℂ (.of Γ(X, opens i)) (I.ideal (opens i))
      (equations i) (divided i)

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : GlobalMixedCenterAtlas f I D)

def GlobalMixedCenterAtlas.reesCover [IsIntegral X] [IsLocallyNoetherian X] (hI : I ≠ ⊥) :
    (GlobalBlowup.Data.Construction.globalBlowup I hI).AffineOpenCover :=
  ChosenGlobalReesCover.Construction.globalBlowupChosenReesAffineCover I hI A.opens A.cover (fun i => I.ideal (A.opens i))
    (fun _ d => d) (fun _ => by
      apply le_antisymm
      · apply Ideal.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact j.property
      · intro x hx
        exact Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩)

def GlobalMixedCenterAtlas.blowupBoundary [IsIntegral X] [IsLocallyNoetherian X] [Fintype β]
    (hI : I ≠ ⊥) :
    MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
      (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) [Finset.univ] := by
  let Q := A.reesCover hI
  let : ∀ i, Algebra ℂ Γ(X, A.opens i) := fun i => Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  let : ∀ p : Q.I₀, Algebra ℂ (Q.X p) := fun p =>
    Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra ℂ (I.ideal (A.opens p.1)) p.2
  let v (p : Q.I₀) : Option β → Q.X p :=
    MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal (A.opens p.1)) p.2 (A.divided p.1)
      (A.equations p.1) (A.contained p.1)
  have hb (p : Q.I₀) : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (Q.X p) (v p) :=
    MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, A.opens p.1))
      (I.ideal (A.opens p.1)) (A.equations p.1) (A.divided p.1) (A.contained p.1)
      (A.boundary p.1) (A.center p.1) p.2
  apply MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.ofAffineCover (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
    (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) [Finset.univ] Q
    (fun p => GlobalControlled.DifferentialBound.Construction.globalBlowupReesChart_complex_structure f I hI (A.opens p.1) p.2) v
  · intro p j
    exact CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_comap_reesChart I hI D (A.divided p.1)
      (A.opens p.1) (A.equations p.1) (A.component p.1) (A.contained p.1) p.2 (hb p) j
  · exact hb
  · intro p
    exact Boundary.Schedule.Construction.boundaryFacesCover_univ (v p)

theorem GlobalMixedCenterAtlas.locally_monomial_transform
    [IsIntegral X] [IsLocallyNoetherian X] [Fintype β]
    (M : X.IdealSheafData) (hI : I ≠ ⊥) (a : A.indices → β → ℕ) (b : ℕ)
    (hM : ∀ i, M.ideal (A.opens i) = Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (A.equations i) (a i)})
    (hb : ∀ i, b ≤ Boundary.MonomialSchedule.Construction.boundaryFaceWeight (a i) (A.divided i))
    (p : (A.reesCover hI).I₀) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI b).comap ((A.reesCover hI).f p) =
      (MixedBoundary.Construction.boundaryMonomialSheaf (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)
        (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents (a p.1) b (A.divided p.1))).comap ((A.reesCover hI).f p) := by
  let : Algebra ℂ Γ(X, A.opens p.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens p.1)
  exact CanonicalBoundaryTransform.Construction.global_canonical_boundary_locally_monomial_transform_on_chart I M hI D
    (A.divided p.1) (a p.1) b (hb p.1) (A.opens p.1) (A.equations p.1) (A.component p.1)
    (hM p.1) (A.contained p.1) p.2
    (MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, A.opens p.1))
      (I.ideal (A.opens p.1)) (A.equations p.1) (A.divided p.1) (A.contained p.1)
      (A.boundary p.1) (A.center p.1) p.2)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryAtlas.Construction
