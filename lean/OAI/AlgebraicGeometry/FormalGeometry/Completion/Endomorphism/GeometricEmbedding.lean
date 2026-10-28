import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapFaithful
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Geometric Embedding -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding

noncomputable section

/-! Actual endomorphisms, and their rationalizations, inject into the
endomorphisms after geometric base change. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.CategoryTheory.Obj

namespace Construction

universe u

variable (K : Type u) [Field K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]

def algebraicEndGeometricBaseChange : Endomorphisms.Construction.AlgebraicEnd A →+* Endomorphisms.Construction.AlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver K A) where
  toFun f := Additive.ofMul (Grp.ofHom
    ((Over.pullback (Geometric.Frobenius.Construction.algebraicClosureBase K)).map f.toMul.hom.hom))
  map_one' := by
    apply Grp.hom_ext
    exact (Over.pullback (Geometric.Frobenius.Construction.algebraicClosureBase K)).map_id A
  map_mul' f g := by
    apply Grp.hom_ext
    exact (Over.pullback (Geometric.Frobenius.Construction.algebraicClosureBase K)).map_comp g.toMul.hom.hom f.toMul.hom.hom
  map_zero' := by
    apply Grp.hom_ext
    exact (Over.pullback (Geometric.Frobenius.Construction.algebraicClosureBase K)).map_one
  map_add' f g := by
    apply Grp.hom_ext
    exact (Over.pullback (Geometric.Frobenius.Construction.algebraicClosureBase K)).map_mul f.toMul.hom.hom g.toMul.hom.hom

theorem algebraicEndGeometricBaseChange_injective :
    Function.Injective (algebraicEndGeometricBaseChange K A) := by
  intro f g h
  have he := congrArg (fun t : Endomorphisms.Construction.AlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver K A) => t.toMul.hom.hom.left) h
  have hfg := Geometric.MapFaithful.Construction.geometricFiberMap_injective K he
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact hfg

def rationalAlgebraicEndGeometricEmbedding :
    Endomorphisms.Construction.RationalAlgebraicEnd A →ₗ[ℚ] Endomorphisms.Construction.RationalAlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver K A) := by
  let : Ring (Endomorphisms.Construction.AlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver K A)) := Endomorphisms.Construction.algebraicEndRing _
  exact (algebraicEndGeometricBaseChange K A).toIntAlgHom.toLinearMap.baseChange ℚ

theorem rationalAlgebraicEndGeometricEmbedding_injective :
    Function.Injective (rationalAlgebraicEndGeometricEmbedding K A) := by
  let : Ring (Endomorphisms.Construction.AlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver K A)) := Endomorphisms.Construction.algebraicEndRing _
  have : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  unfold rationalAlgebraicEndGeometricEmbedding
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (algebraicEndGeometricBaseChange_injective K A)

theorem rationalAlgebraicEnd_finiteDimensional_of_geometric
    [FiniteDimensional ℚ (Endomorphisms.Construction.RationalAlgebraicEnd (Geometric.Frobenius.Construction.geometricFiberOver K A))] :
    FiniteDimensional ℚ (Endomorphisms.Construction.RationalAlgebraicEnd A) :=
  FiniteDimensional.of_injective (rationalAlgebraicEndGeometricEmbedding K A)
    (rationalAlgebraicEndGeometricEmbedding_injective K A)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding
