import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Prod
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOrientation

/-! # Complex Normal Eq -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalEq.Cycles

/-!
# Linear normal spaces of complex coordinate submanifolds

These are concrete local linear models for normal directions to a smooth
complex submanifold. The normal space is the actual quotient of the ambient
complex vector space by its tangent subspace. No cycle class or Thom class is
postulated here.
-/

variable {V W U : Type*}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup U] [Module ℂ U]

/-- The complex linear normal space to a complex subspace. -/
abbrev ComplexNormal (S : Submodule ℂ V) := V ⧸ S

/-- Normal vectors are ambient vectors modulo the tangent subspace. -/
abbrev normalProjection (S : Submodule ℂ V) : V →ₗ[ℂ] ComplexNormal S := S.mkQ

@[simp]
theorem normalProjection_eq_zero (S : Submodule ℂ V) (v : V) :
    normalProjection S v = 0 ↔ v ∈ S := by
  exact Submodule.Quotient.mk_eq_zero S

/-- An ambient complex coordinate change carrying tangent spaces to tangent
spaces induces a complex linear change of normal coordinates. -/
def complexNormalEquiv (S : Submodule ℂ V) (T : Submodule ℂ W)
    (e : V ≃ₗ[ℂ] W) (he : S.map e.toLinearMap = T) :
    ComplexNormal S ≃ₗ[ℂ] ComplexNormal T :=
  Submodule.Quotient.equiv S T e he

@[simp]
theorem complexNormalEquiv_projection (S : Submodule ℂ V) (T : Submodule ℂ W)
    (e : V ≃ₗ[ℂ] W) (he : S.map e.toLinearMap = T) (v : V) :
    complexNormalEquiv S T e he (normalProjection S v) = normalProjection T (e v) := by
  rfl

theorem complexNormalEquiv_trans (S : Submodule ℂ V) (T : Submodule ℂ W)
    (R : Submodule ℂ U) (e : V ≃ₗ[ℂ] W) (f : W ≃ₗ[ℂ] U)
    (he : S.map e.toLinearMap = T) (hf : T.map f.toLinearMap = R)
    (hef : S.map (e.trans f).toLinearMap = R) :
    complexNormalEquiv S R (e.trans f) hef =
      (complexNormalEquiv S T e he).trans (complexNormalEquiv T R f hf) := by
  exact Submodule.Quotient.equiv_trans S T R e f he hf hef

/-- The real linear normal quotient agrees with restriction of scalars of the
complex normal quotient. -/
def realNormalEquiv (S : Submodule ℂ V) :
    (V ⧸ S.restrictScalars ℝ) ≃ₗ[ℝ] ComplexNormal S :=
  Submodule.Quotient.restrictScalarsEquiv ℝ S

@[simp]
theorem realNormalEquiv_projection (S : Submodule ℂ V) (v : V) :
    realNormalEquiv S ((S.restrictScalars ℝ).mkQ v) = normalProjection S v := by
  rfl

theorem complexNormal_finrank [FiniteDimensional ℂ V] (S : Submodule ℂ V) :
    Module.finrank ℂ (ComplexNormal S) = Module.finrank ℂ V - Module.finrank ℂ S := by
  exact S.finrank_quotient

/-- A complex normal space of dimension `p` has real dimension `2 * p`. -/
theorem complexNormal_real_finrank (S : Submodule ℂ V) :
    Module.finrank ℝ (ComplexNormal S) = 2 * Module.finrank ℂ (ComplexNormal S) := by
  exact finrank_real_of_complex (ComplexNormal S)

theorem realNormal_finrank [FiniteDimensional ℂ V] (S : Submodule ℂ V) :
    Module.finrank ℝ (V ⧸ S.restrictScalars ℝ) =
      2 * (Module.finrank ℂ V - Module.finrank ℂ S) := by
  rw [(realNormalEquiv S).finrank_eq, complexNormal_real_finrank, complexNormal_finrank]

theorem complexNormal_finrank_invariant (S : Submodule ℂ V) (T : Submodule ℂ W)
    (e : V ≃ₗ[ℂ] W) (he : S.map e.toLinearMap = T) :
    Module.finrank ℂ (ComplexNormal S) = Module.finrank ℂ (ComplexNormal T) :=
  (complexNormalEquiv S T e he).finrank_eq

/-- A complex coordinate change preserving the tangent space induces a
positive real determinant on the normal space. -/
theorem complexNormalEquiv_realDet_pos (S : Submodule ℂ V)
    (e : V ≃ₗ[ℂ] V) (he : S.map e.toLinearMap = S) :
    0 < LinearMap.det (((complexNormalEquiv S S e he).restrictScalars ℝ).toLinearMap) := by
  exact ComplexOrientation.complexLinearEquiv_realDet_pos (complexNormalEquiv S S e he)

/-- The canonical complex orientation of the normal quotient, expressed using
its finite complex basis. Independence of that basis is proved below. -/
noncomputable def complexNormalOrientation [FiniteDimensional ℂ V] (S : Submodule ℂ V) :
    Orientation ℝ (ComplexNormal S)
      (Fin (Module.finrank ℂ (ComplexNormal S)) × Fin 2) :=
  ComplexOrientation.complexOrientationOfBasis (Module.finBasis ℂ (ComplexNormal S))

theorem complexNormalOrientation_eq_basis [FiniteDimensional ℂ V] (S : Submodule ℂ V)
    (b : Module.Basis (Fin (Module.finrank ℂ (ComplexNormal S))) ℂ (ComplexNormal S)) :
    complexNormalOrientation S = ComplexOrientation.complexOrientationOfBasis b := by
  exact ComplexOrientation.complexOrientationOfBasis_eq (Module.finBasis ℂ (ComplexNormal S)) b

/-- The quotient orientation is preserved by every ambient complex linear
coordinate change preserving the tangent subspace. -/
theorem complexNormalEquiv_preserves_orientation [FiniteDimensional ℂ V]
    (S : Submodule ℂ V) (e : V ≃ₗ[ℂ] V) (he : S.map e.toLinearMap = S) :
    Orientation.map (Fin (Module.finrank ℂ (ComplexNormal S)) × Fin 2)
      ((complexNormalEquiv S S e he).restrictScalars ℝ) (complexNormalOrientation S) =
      complexNormalOrientation S := by
  exact ComplexOrientation.complexLinearEquiv_preserves_realBasis_orientation
    (ComplexOrientation.complexRealBasis (Module.finBasis ℂ (ComplexNormal S))) (complexNormalEquiv S S e he)

/-- In local product coordinates, the coordinate submanifold has zero normal
coordinate. -/
def coordinateTangent (n p : ℕ) :
    Submodule ℂ ((Fin n → ℂ) × (Fin p → ℂ)) :=
  LinearMap.ker (LinearMap.snd ℂ (Fin n → ℂ) (Fin p → ℂ))

@[simp]
theorem mem_coordinateTangent (n p : ℕ) (x : (Fin n → ℂ) × (Fin p → ℂ)) :
    x ∈ coordinateTangent n p ↔ x.2 = 0 := by
  rfl

/-- The quotient normal space to a coordinate `n`-plane in `ℂⁿ × ℂᵖ`
is precisely the displayed `ℂᵖ` factor. -/
noncomputable def coordinateNormalEquiv (n p : ℕ) :
    ComplexNormal (coordinateTangent n p) ≃ₗ[ℂ] (Fin p → ℂ) :=
  (LinearMap.snd ℂ (Fin n → ℂ) (Fin p → ℂ)).quotKerEquivOfSurjective
    (fun y => ⟨(0, y), rfl⟩)

@[simp]
theorem coordinateNormalEquiv_projection (n p : ℕ)
    (x : (Fin n → ℂ) × (Fin p → ℂ)) :
    coordinateNormalEquiv n p (normalProjection (coordinateTangent n p) x) = x.2 := by
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

@[simp]
theorem coordinateNormal_complex_finrank (n p : ℕ) :
    Module.finrank ℂ (ComplexNormal (coordinateTangent n p)) = p := by
  rw [(coordinateNormalEquiv n p).finrank_eq]
  simp

@[simp]
theorem coordinateNormal_real_finrank (n p : ℕ) :
    Module.finrank ℝ (ComplexNormal (coordinateTangent n p)) = 2 * p := by
  rw [complexNormal_real_finrank, coordinateNormal_complex_finrank]

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalEq.Cycles
