import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.AtlasBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.SequenceCompatibility

/-! # Intersection Canonical -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Boundary-intersection blowups have the actual canonical boundary required by sequence compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersectionCenterAtlas
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type}
    {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (C : Finset β) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) D where
  indices := A.indices
  opens := A.opens
  cover := A.cover
  equations := A.equations
  component := A.component
  divided := fun _ => C
  contained := A.intersection_mem C
  boundary := A.boundary
  center := by
    intro i
    let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
    rw [A.intersection_ideal C i]
    exact (A.boundary i).intersection_center C

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersection_canonical_eq_mixed
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {β : Type} {D : β → X.IdealSheafData} {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (C : Finset β)
    (hI : GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C ≠ ⊥) :
    CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI D =
      Global.MixedBoundary.Construction.globalBlowupMixedBoundary (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI D C := by
  let I := GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C
  let B := A.intersectionCenterAtlas C
  let Q := B.reesCover hI
  funext j
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ Q.openCover
  intro p
  let : Algebra ℂ Γ(X, B.opens p.1) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (B.opens p.1)
  have hb : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts ℂ (.of (Blowup.Charts.Construction.blowupChart (I.ideal (B.opens p.1)) p.2))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal (B.opens p.1)) p.2 C (B.equations p.1) (B.contained p.1)) :=
    MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup (.of Γ(X, B.opens p.1))
      (I.ideal (B.opens p.1)) (B.equations p.1) C (B.contained p.1)
      (B.boundary p.1) (B.center p.1) p.2
  exact (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary_comap_reesChart I hI D C (B.opens p.1)
    (B.equations p.1) (B.component p.1) (B.contained p.1) p.2 hb j).trans
      (Global.MixedBoundary.Construction.globalBlowupMixedBoundary_comap_reesChart I hI D C (B.opens p.1)
        (B.equations p.1) (B.component p.1) (B.contained p.1) p.2 j).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
