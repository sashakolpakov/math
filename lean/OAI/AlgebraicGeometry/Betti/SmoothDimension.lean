import OAI.AlgebraicGeometry.Betti.AffineDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth Dimension -/

namespace OAI.AlgebraicGeometry.Betti.SmoothDimension.Realization

noncomputable section

/-!
# A common relative dimension for an integral smooth scheme over a field

Every nonempty affine neighborhood uses the same function-field differential
dimension. This supplies a single dimension for the analytic chart assembly;
it is a consequence of smoothness and integrality rather than an additional
field attached to the variety.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} [IsIntegral X]

/-- On a nonempty affine open, standard smoothness has the common function-field
relative dimension, for the actual base-section algebra structure. -/
theorem affineStandardSmooth_dimension (f : X ⟶ Y) (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) :
    letI := AffineDimension.Realization.sectionBaseAlgebra f U
    Algebra.IsStandardSmooth Γ(Y, ⊤) Γ(X, U) →
      Algebra.IsStandardSmoothOfRelativeDimension (AffineDimension.Realization.functionFieldDifferentialDimension f)
        Γ(Y, ⊤) Γ(X, U) := by
  let := AffineDimension.Realization.sectionBaseAlgebra f U
  let := AffineDimension.Realization.functionFieldBaseAlgebra f
  let := AffineDimension.Realization.functionFieldBase_isScalarTower f U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  intro h
  let := h
  exact Foundations.Scheme.DifferentialRankLocalization.Algebraic.standardSmooth_has_fraction_differential_dimension
    (R := Γ(Y, ⊤)) (S := Γ(X, U)) (T := X.functionField)

/-- An integral smooth scheme over a field has one relative dimension,
computed from its genuine function field. -/
theorem smoothOfFunctionFieldDimension {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [Smooth f] :
    SmoothOfRelativeDimension (AffineDimension.Realization.functionFieldDifferentialDimension f) f := by
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  have hUtop : U = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      have hfx : f x ∈ U := e hx
      have heq : f x = y := Subsingleton.elim _ _
      change y ∈ U
      exact heq ▸ hfx
  subst U
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  refine ⟨⊤, hU, V, hV, hx, e, ?_⟩
  exact affineStandardSmooth_dimension f V hV hstd

end

end OAI.AlgebraicGeometry.Betti.SmoothDimension.Realization
