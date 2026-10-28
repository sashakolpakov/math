import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Subalgebra Recovery Spec -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraRecoverySpec

noncomputable section

/-! The canonical recovery morphism for a coefficient subalgebra, with its ring structure fixed at definition time. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

abbrev subalgebraBaseScheme
    {C : Type v} {R : Type u} [CommRing C] [CommRing R] [Algebra C R] (D : Subalgebra C R) : Scheme.{u} :=
  Spec (.of D)

def subalgebraRecoverySpec
    {C : Type v} {R : Type u} [CommRing C] [CommRing R] [Algebra C R] (D : Subalgebra C R) :
    Spec (.of R) ⟶ subalgebraBaseScheme D := Spec.map (CommRingCat.ofHom D.val.toRingHom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraRecoverySpec
