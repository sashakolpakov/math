import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryBlowupPreservation

/-! # Local Boundary Property -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A local boundary property expressed by actual pointed affine open coordinate models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts (k : Type u) [CommRing k] (R : CommRingCat.{u})
    [Algebra k R] {ι : Type v} (w : ι → R) : Prop :=
  ∀ p : PrimeSpectrum R, Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p)

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.hasEtaleBoundaryCharts {k : Type u} [CommRing k]
    {R : CommRingCat.{u}} [Algebra k R] {ι : Type v} {w : ι → R}
    (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w := by
  intro p
  refine ⟨{ carrier := R
            algebra := inferInstance
            map := AlgHom.id k R
            isOpenImmersion := ?_
            point := p
            point_over := ?_
            model := M }⟩
  · change IsOpenImmersion (Spec.map (𝟙 R))
    rw [Spec.map_id]
    infer_instance
  · exact PrimeSpectrum.ext rfl

variable (k : Type u) [Field k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The actual local property survives each framed blowup whose center
lies in every selected boundary component, with the new exceptional
component included in the output family. -/
theorem LocalBoundaryProperty.Construction.hasEtaleBoundaryCharts_blowup
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R] (I : Ideal R)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range g) = I)
    {θ : Type v} [Fintype θ] (w : θ → R) (hw : ∀ j, w j ∈ I)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (a : I) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I a))
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw) := by
  intro p
  obtain ⟨C⟩ := hboundary (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p)
  exact LocalBoundaryBlowupPreservation.Construction.exists_boundary_blowup_open_chart_of_local_model k R I g D hD hgen w hw a p C

/-- Retaining just the old labels gives the same local property for
the actual divided family used by a boundary-control phase. -/
theorem LocalBoundaryProperty.Construction.hasEtaleBoundaryCharts_divided_boundary
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R] (I : Ideal R)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range g) = I)
    {θ : Type u} [Fintype θ] (w : θ → R) (hw : ∀ j, w j ∈ I)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (a : I) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I a)) (Boundary.FamilyTransform.Construction.blowupBoundaryFamily I a w hw) := by
  intro p
  obtain ⟨C⟩ := LocalBoundaryProperty.Construction.hasEtaleBoundaryCharts_blowup k R I g D hD hgen w hw hboundary a p
  exact ⟨C.reindex ⟨some, Option.some_injective θ⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
