import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Complex Point Existence -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme

noncomputable section

/-!
# Existence of genuine complex-valued points

For an actual complex scheme locally of finite type, relative morphisms from
`Spec ℂ` are identified with closed scheme points using mathlib's proved
algebraically closed residue-field theorem. A nonempty such scheme consequently
has a complex-valued point. This file does not equip these points with a topology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme}

/-- Relative scheme points are precisely scheme morphisms whose composite with
the structure map is the identity of the base. -/
def ComplexPointExistence.complexOverPointsEquivSections (f : X ⟶ ProjectiveSpace.complexBase) :
    (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Over.mk f) ≃
      {p : ProjectiveSpace.complexBase ⟶ X // p ≫ f = 𝟙 ProjectiveSpace.complexBase} where
  toFun p := ⟨p.left, p.w⟩
  invFun p := Over.homMk p.val p.property
  left_inv p := by ext; rfl
  right_inv p := by rfl

/-- For schemes locally of finite type over `ℂ`, actual complex-valued points
correspond exactly to closed scheme points. -/
def ComplexPointExistence.complexOverPointsEquivClosedPoints (f : X ⟶ ProjectiveSpace.complexBase)
    [LocallyOfFiniteType f] :
    (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Over.mk f) ≃ closedPoints X :=
  (ComplexPointExistence.complexOverPointsEquivSections f).trans (pointEquivClosedPoint f)

/-- A nonempty complex scheme locally of finite type has a closed scheme point. -/
theorem ComplexPointExistence.exists_closedPoint_of_nonempty (f : X ⟶ ProjectiveSpace.complexBase)
    [LocallyOfFiniteType f] [Nonempty X] : ∃ x : X, IsClosed ({x} : Set X) := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := X) Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨x, hx⟩

/-- Existence of a complex-valued point is proved from scheme nonemptiness,
not added as an extra field of a variety. -/
theorem ComplexPointExistence.nonempty_complexOverPoints (f : X ⟶ ProjectiveSpace.complexBase)
    [LocallyOfFiniteType f] [Nonempty X] :
    Nonempty (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Over.mk f) := by
  obtain ⟨x, hx⟩ := ComplexPointExistence.exists_closedPoint_of_nonempty f
  exact ⟨(ComplexPointExistence.complexOverPointsEquivClosedPoints f).symm ⟨x, hx⟩⟩

/-- For schemes locally of finite type over `ℂ`, the genuine complex-point type
is nonempty if and only if the underlying scheme is nonempty. -/
theorem ComplexPointExistence.nonempty_complexOverPoints_iff (f : X ⟶ ProjectiveSpace.complexBase)
    [LocallyOfFiniteType f] :
    Nonempty (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ Over.mk f) ↔ Nonempty X := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.left (IsLocalRing.closedPoint ℂ)⟩
  · intro hX
    let : Nonempty X := hX
    exact ComplexPointExistence.nonempty_complexOverPoints f

/-- Every integral smooth projective variety in our algebraic domain has an
actual complex-valued point over its given `Spec ℂ` base. -/
theorem IntegralProjective.IntegralProjectiveVariety.complexPoints_nonempty (V : IntegralProjective.IntegralProjectiveVariety) :
    Nonempty (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ V.toOver) :=
  ComplexPointExistence.nonempty_complexOverPoints V.structureMap

end

end OAI.AlgebraicGeometry.Foundations.Scheme
