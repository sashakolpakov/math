import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MonomialBoundaryAtlas
import OAI.AlgebraicGeometry.Resolution.Blowups.NamedBoundaryIntersectionCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.MonomialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.DifferentialBound

/-! # Atlas Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The common boundary-intersection step propagates the full native atlas across the global blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β : Type}
    {D : β → X.IdealSheafData} {L : List (Finset β)} (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L)

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersection_ideal (C : Finset β) (i : A.indices) :
    (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C).ideal (A.opens i) = Boundary.CountReduction.Construction.boundaryIntersectionIdeal (A.equations i) C :=
  GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf_local_equations D C (A.opens i) (A.equations i) (fun j _ => A.component i j)

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersection_mem (C : Finset β) (i : A.indices)
    (j : β) (hj : j ∈ C) : A.equations i j ∈ (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C).ideal (A.opens i) := by
  rw [A.intersection_ideal C i]
  exact Boundary.Schedule.Construction.boundaryIntersection_mem (A.equations i) C j hj

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersectionGenerators (C : Finset β) (i : A.indices) :
    C → (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C).ideal (A.opens i) :=
  fun j => ⟨A.equations i j.val, A.intersection_mem C i j.val j.property⟩

theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersectionGenerators_span (C : Finset β) (i : A.indices) :
    Ideal.span (Set.range (fun j => (A.intersectionGenerators C i j).val)) =
      (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C).ideal (A.opens i) := (A.intersection_ideal C i).symm

variable [IsIntegral X] [IsLocallyNoetherian X]

include A in
theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersection_blowup_smooth (C : Finset β)
    (hI : GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C ≠ ⊥) :
    Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI ≫ f) := by
  apply Global.CenterSmooth.Construction.globalBlowup_smooth_of_affine_cover _ hI f A.opens A.cover
  intro i
  let : Algebra ℂ Γ(X, A.opens i) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  rw [← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (A.opens i), A.intersection_ideal C i]
  exact (A.boundary i).intersection_blowup_smooth C

def Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.blowupIntersection (C : Finset β) [DecidableEq β]
    (hI : GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C ≠ ⊥) :
    Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas
      (GlobalBlowup.Data.Construction.globalBlowupToBase (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI ≫ f)
      (Global.MixedBoundary.Construction.globalBlowupMixedBoundary (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI D C) (Boundary.MonomialSchedule.Construction.boundaryScheduleFaces C L) := by
  let I := GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C
  let g := A.intersectionGenerators C
  let Q := ChosenGlobalReesCover.Construction.globalBlowupChosenReesAffineCover I hI A.opens A.cover (fun _ => C) g
    (A.intersectionGenerators_span C)
  let : ∀ i, Algebra ℂ Γ(X, A.opens i) := fun i => Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
  let : ∀ p : Q.I₀, Algebra ℂ (Q.X p) := fun p =>
    Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra ℂ (I.ideal (A.opens p.1)) (g p.1 p.2)
  let v (p : Q.I₀) : Option β → Q.X p :=
    MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal (A.opens p.1)) (g p.1 p.2) C (A.equations p.1)
      (A.intersection_mem C p.1)
  apply Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.ofAffineCover
    (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (Global.MixedBoundary.Construction.globalBlowupMixedBoundary I hI D C) (Boundary.MonomialSchedule.Construction.boundaryScheduleFaces C L) Q
    (fun p => GlobalControlled.DifferentialBound.Construction.globalBlowupReesChart_complex_structure f I hI (A.opens p.1) (g p.1 p.2)) v
  · intro p j
    exact Global.MixedBoundary.Construction.globalBlowupMixedBoundary_comap_reesChart I hI D C (A.opens p.1) (A.equations p.1)
      (A.component p.1) (A.intersection_mem C p.1) (g p.1 p.2) j
  · intro p
    exact (A.boundary p.1).blowup_named_intersection (I.ideal (A.opens p.1)) C
      (A.intersection_ideal C p.1) p.2 (g p.1 p.2) rfl (A.intersection_mem C p.1)
  · intro p
    exact (A.faces p.1).blowup_named_intersection (I.ideal (A.opens p.1)) C
      (A.intersection_ideal C p.1) p.2 (g p.1 p.2) rfl (A.intersection_mem C p.1)

include A in
theorem Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.monomial_transform [Fintype β]
    (C : Finset β) (hI : GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C ≠ ⊥) (a : β → ℕ) (b : ℕ)
    (hb : b ≤ Boundary.MonomialSchedule.Construction.boundaryFaceWeight a C) :
    GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI b =
      Global.MixedBoundary.Construction.boundaryMonomialSheaf (Global.MixedBoundary.Construction.globalBlowupMixedBoundary (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI D C)
        (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a b C) :=
  GlobalBoundary.MonomialTransform.Construction.global_boundary_monomial_transform _ hI D C a b hb A.opens A.cover
    (fun _ => C) (A.intersectionGenerators C) (A.intersectionGenerators_span C)
    A.equations A.component (A.intersection_mem C)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
