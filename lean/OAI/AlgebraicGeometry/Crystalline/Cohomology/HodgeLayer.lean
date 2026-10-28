import OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeTruncationIs
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Hodge Layer -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeLayer.HodgeLayerDerivedFiniteness

noncomputable section

/-! # Finite Ext groups give finite derived cohomology of each original Hodge layer -/

open _root_.CategoryTheory Limits

universe u v w z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasDerivedCategory.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (A : C) (K : CochainComplex C ℕ)

def shiftedLayerIso (r n : ℕ) (hr : r ≤ n) :
    (DerivedCategory.Q.obj ((HodgeTruncationIs.HodgeTruncationLayer.layer K r).extend ComplexShape.embeddingUpNat))⟦(n : ℤ)⟧ ≅
      ((DerivedCategory.singleFunctor C 0).obj (K.X r))⟦((n - r : ℕ) : ℤ)⟧ :=
  (shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso
    (DerivedCategory.Q.mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (K.X r) r (r : ℤ) rfl)) ≪≫
    ((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) ((r : ℤ) - n) (r : ℤ) (by omega)).app (K.X r) ≪≫
      (((DerivedCategory.singleFunctors C).shiftIso ((n - r : ℕ) : ℤ) ((r : ℤ) - n) 0
        (by omega)).app (K.X r)).symm

theorem layer_finite (r n : ℕ) (hr : r ≤ n) [Module.Finite R (Abelian.Ext.{w} A (K.X r) (n - r))] :
    Module.Finite R ((DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj ((HodgeTruncationIs.HodgeTruncationLayer.layer K r).extend ComplexShape.embeddingUpNat))⟦(n : ℤ)⟧) := by
  let : Module.Finite R ((DerivedCategory.singleFunctor C 0).obj A ⟶
      ((DerivedCategory.singleFunctor C 0).obj (K.X r))⟦((n - r : ℕ) : ℤ)⟧) :=
    Module.Finite.equiv (Abelian.Ext.homLinearEquiv (R := R))
  exact Module.Finite.equiv
    (Linear.homCongr R (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A))
      (shiftedLayerIso K r n hr).symm)

def tail (r : ℕ) : CochainComplex C ℤ :=
  (HodgeFiltrationD.HodgeFiltration.brutal K r).extend ComplexShape.embeddingUpNat

omit [HasExt.{w} C] in
theorem last_tail_finite (n : ℕ) :
    Module.Finite R ((DerivedCategory.singleFunctor C 0).obj A ⟶
      (DerivedCategory.Q.obj (tail K (n + 1)))⟦(n : ℤ)⟧) := by
  let L := tail K (n + 1)
  let : L.IsStrictlyGE ((n + 1 : ℕ) : ℤ) :=
    NumberTheory.PadicHodge.GeometricComparison.TruncationBoundsGE.TruncationBounds.extended_isStrictlyGE K ((n + 1 : ℕ) : ℤ)
  let : (L⟦(n : ℤ)⟧).IsStrictlyGE 1 := L.isStrictlyGE_shift ((n + 1 : ℕ) : ℤ) n 1 (by omega)
  let P := (CochainComplex.singleFunctor C 0).obj A
  let : Subsingleton (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (L⟦(n : ℤ)⟧)) :=
    DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE P (L⟦(n : ℤ)⟧) 0 1 (by omega)
  let : Module.Finite R (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (L⟦(n : ℤ)⟧)) :=
    Module.Finite.of_finite
  let e : (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (L⟦(n : ℤ)⟧)) ≃ₗ[R]
      (DerivedCategory.Q.obj P ⟶ (DerivedCategory.Q.obj L)⟦(n : ℤ)⟧) :=
    Linear.homCongr R (Iso.refl (DerivedCategory.Q.obj P)) ((DerivedCategory.Q.commShiftIso (n : ℤ)).app L)
  exact Module.Finite.equiv e

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeLayer.HodgeLayerDerivedFiniteness
