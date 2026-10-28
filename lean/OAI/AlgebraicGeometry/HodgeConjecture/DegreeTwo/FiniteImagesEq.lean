import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence
import Mathlib.Topology.Irreducible

/-! # Finite Images Eq -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FiniteImagesEq.Constructions.FiniteImages

noncomputable section

/-!
# DegreeTwo: finite algebraic images of an integral variety

An algebraic map with finitely many complex-point values is constant on the
complex points of an irreducible source. The proof uses the density of closed
points and their exact correspondence with complex-valued scheme points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom]
  [LocallyOfFiniteType Y.hom] [IrreducibleSpace X.left]

/-- A finite set of closed points is a closed subset of the scheme. -/
theorem finite_closedPoints_isClosed {T : Type*} [TopologicalSpace T]
    {S : Set T} (hS : S.Finite) (hclosed : S ⊆ closedPoints T) : IsClosed S := by
  simpa only [Set.biUnion_of_singleton] using
    hS.isClosed_biUnion (fun x hx => hclosed hx)

/-- An actual morphism with finite image on complex points is constant when
its source is irreducible. -/
theorem map_eq_of_finite_range (f : X ⟶ Y)
    (hf : (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)).Finite)
    (x y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f y := by
  let cp : Foundations.Scheme.ProjectiveSpace.complexBase := IsLocalRing.closedPoint ℂ
  let ev : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y → Y.left := fun q => q.left cp
  let S : Set Y.left := ev '' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
  have hS : S.Finite := hf.image ev
  have hclosed : S ⊆ closedPoints Y.left := by
    rintro z ⟨q, hq, rfl⟩
    exact ((Foundations.Scheme.ComplexPointExistence.complexOverPointsEquivClosedPoints Y.hom) q).property
  have hcS : IsClosed S := finite_closedPoints_isClosed hS hclosed
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hcl : closedPoints X.left ⊆ f.left ⁻¹' S := by
    intro z hz
    obtain ⟨q, hq⟩ := (Foundations.Scheme.ComplexPointExistence.complexOverPointsEquivClosedPoints X.hom).surjective ⟨z, hz⟩
    have hqz : q.left cp = z := congrArg Subtype.val hq
    refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f q, ⟨q, rfl⟩, ?_⟩
    change f.left (q.left cp) = f.left z
    rw [hqz]
  have hfull : Set.univ ⊆ f.left ⁻¹' S := by
    rw [← closure_closedPoints]
    exact closure_minimal hcl (hcS.preimage f.left.continuous)
  have hrS : Set.range f.left ⊆ S := by
    rintro z ⟨w, rfl⟩
    exact hfull (Set.mem_univ w)
  have hrfinite : (Set.range f.left).Finite := hS.subset hrS
  have hrdiscrete := hrfinite.isDiscrete_of_subset_closedPoints (hrS.trans hclosed)
  have hrpre : IsPreirreducible (Set.range f.left) := by
    simpa only [Set.image_univ] using
      (PreirreducibleSpace.isPreirreducible_univ (X := X.left)).image f.left
        f.left.continuous.continuousOn
  have hsub := hrdiscrete.subsingleton_of_isPreirreducible hrpre
  apply (Foundations.Scheme.ComplexPointExistence.complexOverPointsEquivClosedPoints Y.hom).injective
  apply Subtype.ext
  exact hsub ⟨x.left cp, rfl⟩ ⟨y.left cp, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FiniteImagesEq.Constructions.FiniteImages
