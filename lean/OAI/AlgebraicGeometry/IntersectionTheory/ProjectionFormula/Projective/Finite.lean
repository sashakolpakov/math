import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ProjectionRestriction
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover

/-! # Finite -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Finite

noncomputable section

/-! A projective linear projection restricted to a closed subscheme
disjoint from its center is finite. On each target coordinate chart its
preimage is closed in an affine homogeneous chart of the source projective
space, so properness upgrades affineness to finiteness. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ProjectionRestriction

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
  {X : Scheme} (i : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (hi : ∀ x, i x ∈ BasicOpen.RationalProjection.domain f)

theorem isAffineHom [IsAffineHom i] : IsAffineHom (ProjectionRestriction.projection f i hi) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨j, hj⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen m x
  have hX := MvPolynomial.isHomogeneous_X ℂ j
  refine ⟨Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen m j, hj,
    Proj.isAffineOpen_basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) (MvPolynomial.X j) hX Nat.zero_lt_one, ?_⟩
  change IsAffineOpen (ProjectionRestriction.projection f i hi ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) (MvPolynomial.X j))
  rw [ProjectionRestriction.preimage_basicOpen f i hi (MvPolynomial.X j) hX Nat.zero_lt_one]
  exact (Proj.isAffineOpen_basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f (MvPolynomial.X j))
    (f.map_mem hX) Nat.zero_lt_one).preimage i

theorem isFinite [IsClosedImmersion i]
    (hC : ∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z) : IsFinite (ProjectionRestriction.projection f i hi) :=
  IsFinite.iff_isProper_and_isAffineHom.mpr ⟨ProjectionRestriction.isProper f i hi hC, isAffineHom f i hi⟩

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Finite
