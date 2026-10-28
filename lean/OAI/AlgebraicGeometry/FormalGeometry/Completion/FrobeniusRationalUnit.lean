import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalRegularElement
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.FiniteGeneration
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.FrobeniusFlat
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Frobenius Rational Unit -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusRationalUnit

noncomputable section

/-! The actual Frobenius is a unit in the genuine rational endomorphism algebra.
Its geometric faithfully flat map detects equality of endomorphisms. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.Obj TensorProduct

namespace Construction

universe u

variable (k : Type u) [Field k] [Fintype k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A] [Smooth A.hom]

theorem algebraicFrobenius_isRightRegular : IsRightRegular (Endomorphisms.Construction.algebraicFrobenius k A) := by
  let B := Geometric.Frobenius.Construction.geometricFiberOver k A
  let : Ring (Endomorphisms.Construction.AlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver k A)) := Endomorphisms.Construction.algebraicEndRing _
  let : AddMonoid (Endomorphisms.Construction.AlgebraicEnd B) := (Endomorphisms.Construction.algebraicEndRing B).toAddMonoid
  let φ : Endomorphisms.Construction.AlgebraicEnd A →+* Endomorphisms.Construction.AlgebraicEnd B := Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A
  have : IsFinite (Geometric.Frobenius.Construction.geometricSchemeFrobenius k A) := Geometric.MapBaseChange.Construction.geometricSchemeFrobenius_finite k A
  have : Flat (Geometric.Frobenius.Construction.geometricSchemeFrobenius k A) := Geometric.FrobeniusFlat.Construction.geometricSchemeFrobenius_flat k A
  have : Surjective (Geometric.Frobenius.Construction.geometricSchemeFrobenius k A) := Geometric.MapBaseChange.Construction.geometricSchemeFrobenius_surjective k A
  have : Epi (Geometric.Frobenius.Construction.geometricSchemeFrobenius k A) := inferInstance
  intro f g h
  change f * Endomorphisms.Construction.algebraicFrobenius k A = g * Endomorphisms.Construction.algebraicFrobenius k A at h
  apply Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange_injective k A
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  have hh : φ f * φ (Endomorphisms.Construction.algebraicFrobenius k A) = φ g * φ (Endomorphisms.Construction.algebraicFrobenius k A) := by
    rw [← map_mul, ← map_mul, h]
  have he := congrArg (fun t : Endomorphisms.Construction.AlgebraicEnd B => t.toMul.hom.hom.left) hh
  change Geometric.Frobenius.Construction.geometricSchemeFrobenius k A ≫ (φ f).toMul.hom.hom.left =
    Geometric.Frobenius.Construction.geometricSchemeFrobenius k A ≫ (φ g).toMul.hom.hom.left at he
  exact (cancel_epi (Geometric.Frobenius.Construction.geometricSchemeFrobenius k A)).mp he

theorem rationalAlgebraicFrobenius_isUnit [IsProper A.hom] [GeometricallyIntegral A.hom] :
    IsUnit (Endomorphisms.Construction.rationalAlgebraicFrobenius k A) := by
  have : FiniteDimensional ℚ (Endomorphisms.Construction.RationalAlgebraicEnd A) := Endomorphism.FiniteGeneration.Construction.rationalAlgebraicEnd_finiteDimensional A
  exact RationalRegularElement.Construction.isUnit_of_isRightRegular_finiteDimensional _
    (RationalRegularElement.Construction.rationalized_isRightRegular _ (algebraicFrobenius_isRightRegular k A))

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusRationalUnit
