import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Affine Section Finite Type -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType

noncomputable section

/-!
# Finite-type affine sections over the actual scalar ring

The structural map to `Spec K` gives an affine open's sections a `K`-algebra
structure. Local finite type makes this algebra finite type, after transport
through the canonical isomorphism between `K` and global sections of `Spec K`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [CommRing K] {X : Scheme.{u}}

/-- The scalar homomorphism on an affine open is finite type when the
structural morphism is locally of finite type. -/
theorem specSectionScalarMap_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (SpecScalarTransport.specSectionScalarMap f U).FiniteType := by
  exact (RingHom.finiteType_respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of K)).inv (f.appLE ⊤ U le_top)).mpr
      (f.finiteType_appLE (isAffineOpen_top (Spec (.of K))) hU le_top)

/-- An actual affine coordinate algebra of a locally finite-type `K`-scheme
is finite type over `K`. -/
theorem specSectionScalarAlgebra_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := SpecScalarTransport.specSectionScalarAlgebra f U
    Algebra.FiniteType K Γ(X, U) :=
  specSectionScalarMap_finiteType f U hU

end

end OAI.AlgebraicGeometry.Foundations.Scheme.AffineSectionFiniteType
