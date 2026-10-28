import OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusRationalUnit
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Frobenius Unit -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusUnit

noncomputable section

/-! The actual geometric Frobenius is a unit in the full geometric
endomorphism algebra, via the algebra map induced by base change. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.Obj TensorProduct

namespace Construction

universe u

variable (k : Type u) [Field k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]

local instance geometricEndRing : Ring (Endomorphisms.Construction.AlgebraicEnd (Frobenius.Construction.geometricFiberOver k A)) :=
  Endomorphisms.Construction.algebraicEndRing _

local instance geometricEndAddCommGroup : AddCommGroup (Endomorphisms.Construction.AlgebraicEnd (Frobenius.Construction.geometricFiberOver k A)) :=
  (Endomorphisms.Construction.algebraicEndRing _).toAddCommGroup

def rationalAlgebraicEndGeometricBaseChange :
    Endomorphisms.Construction.RationalAlgebraicEnd A →ₐ[ℚ] Endomorphisms.Construction.RationalAlgebraicEnd (Frobenius.Construction.geometricFiberOver k A) := by
  let : Ring (Endomorphisms.Construction.AlgebraicEnd (Frobenius.Construction.geometricFiberOver k A)) := Endomorphisms.Construction.algebraicEndRing _
  exact Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A).toIntAlgHom

theorem rationalAlgebraicEndGeometricBaseChange_tmul (r : ℚ) (f : Endomorphisms.Construction.AlgebraicEnd A) :
    rationalAlgebraicEndGeometricBaseChange k A (r ⊗ₜ[ℤ] f) =
      r ⊗ₜ[ℤ] Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A f := rfl

variable [Fintype k]

def geometricRationalAlgebraicFrobenius : Endomorphisms.Construction.RationalAlgebraicEnd (Frobenius.Construction.geometricFiberOver k A) :=
  (1 : ℚ) ⊗ₜ[ℤ] Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (Endomorphisms.Construction.algebraicFrobenius k A)

theorem rationalAlgebraicEndGeometricBaseChange_frobenius :
    rationalAlgebraicEndGeometricBaseChange k A (Endomorphisms.Construction.rationalAlgebraicFrobenius k A) =
      geometricRationalAlgebraicFrobenius k A := rfl

variable [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]

theorem geometricRationalAlgebraicFrobenius_isUnit :
    IsUnit (geometricRationalAlgebraicFrobenius k A) := by
  let : Ring (Endomorphisms.Construction.AlgebraicEnd (Frobenius.Construction.geometricFiberOver k A)) := Endomorphisms.Construction.algebraicEndRing _
  exact (FrobeniusRationalUnit.Construction.rationalAlgebraicFrobenius_isUnit k A).map
    (rationalAlgebraicEndGeometricBaseChange k A).toMonoidHom

def geometricRationalAlgebraicFrobeniusUnit : (Endomorphisms.Construction.RationalAlgebraicEnd (Frobenius.Construction.geometricFiberOver k A))ˣ :=
  (geometricRationalAlgebraicFrobenius_isUnit k A).unit

theorem geometricRationalAlgebraicFrobeniusUnit_val :
    (geometricRationalAlgebraicFrobeniusUnit k A).val = geometricRationalAlgebraicFrobenius k A :=
  (geometricRationalAlgebraicFrobenius_isUnit k A).unit_spec

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusUnit
