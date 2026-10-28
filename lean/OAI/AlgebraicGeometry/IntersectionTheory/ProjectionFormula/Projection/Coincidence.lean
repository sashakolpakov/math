import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialPairs
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceClosedPointTest

/-! # Coincidence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Coincidence

noncomputable section

/-! Closed coincidence loci for partial linear projections on an
arbitrary scheme of pairs of points of a projective presentation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

instance target_separated (k : ℕ) : IsSeparated (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k)).hom :=
  inferInstanceAs (IsSeparated (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k))

instance target_finiteType (k : ℕ) : LocallyOfFiniteType (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k)).hom :=
  inferInstanceAs (LocallyOfFiniteType (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k))

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u v : T ⟶ X.toOver)

def domain : T.left.Opens :=
  u.left ⁻¹ᵁ PartialLinear.Projection.domain X k L ⊓
    v.left ⁻¹ᵁ PartialLinear.Projection.domain X k L

theorem projection_over (U : T.left.Opens)
    (hU : U ≤ u.left ⁻¹ᵁ PartialLinear.Projection.domain X k L) :
    (u.left.resLE (PartialLinear.Projection.domain X k L) U hU ≫
      PartialLinear.Projection.map X k L) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k = U.ι ≫ T.hom := by
  rw [Category.assoc, PartialLinear.Projection.over_base,
    ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  exact congrArg (fun f : T.left ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => U.ι ≫ f) u.w

def first : Over.mk ((domain X k L u v).ι ≫ T.hom) ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k) :=
  Over.homMk (u.left.resLE (PartialLinear.Projection.domain X k L) (domain X k L u v) inf_le_left ≫
    PartialLinear.Projection.map X k L) (projection_over X k L u _ inf_le_left)

def second : Over.mk ((domain X k L u v).ι ≫ T.hom) ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k) :=
  Over.homMk (v.left.resLE (PartialLinear.Projection.domain X k L) (domain X k L u v) inf_le_right ≫
    PartialLinear.Projection.map X k L) (projection_over X k L v _ inf_le_right)

def locus : Closeds T.left :=
  CoincidenceClosedPointTest.OpenClosure.locus (domain X k L u v) (first X k L u v) (second X k L u v)

theorem not_mem_of_ne (x : domain X k L u v)
    (hx : (first X k L u v).left x ≠ (second X k L u v).left x) :
    x.val ∉ locus X k L u v :=
  CoincidenceClosedPointTest.OpenClosure.not_mem_of_ne (domain X k L u v)
    (first X k L u v) (second X k L u v) x hx

theorem mem_iff_closed [LocallyOfFiniteType T.hom] (x : domain X k L u v)
    (hx : IsClosed ({x} : Set ((domain X k L u v) : Scheme))) :
    x.val ∈ locus X k L u v ↔ (first X k L u v).left x = (second X k L u v).left x :=
  CoincidenceClosedPointTest.OpenClosure.mem_iff_closed (domain X k L u v)
    (first X k L u v) (second X k L u v) x hx

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Coincidence
