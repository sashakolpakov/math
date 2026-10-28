import OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveDerivedIs
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Connective Derived Equiv -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveDerivedEquiv.ConnectiveDerivedEquivalence

noncomputable section

/-! The connective derived map calculation is linear and natural. -/

open _root_.CategoryTheory

universe u v w

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasDerivedCategory.{w} C]
  {X Y Z : CochainComplex C ℤ}

def equiv (n : ℤ) [X.IsStrictlyGE n] [X.IsStrictlyLE n] [Y.IsStrictlyGE n] :
    (X ⟶ Y) ≃ₗ[R] (DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y) :=
  LinearEquiv.ofBijective (DerivedCategory.Q.mapLinearMap R)
    ⟨ConnectiveDerivedIs.ConnectiveDerivedMaps.injective n, ConnectiveDerivedIs.ConnectiveDerivedMaps.surjective n⟩

theorem naturality (n : ℤ) [X.IsStrictlyGE n] [X.IsStrictlyLE n]
    [Y.IsStrictlyGE n] [Z.IsStrictlyGE n] (a : X ⟶ Y) (f : Y ⟶ Z) :
    equiv R n (a ≫ f) = equiv R n a ≫ DerivedCategory.Q.map f :=
  DerivedCategory.Q.map_comp a f

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveDerivedEquiv.ConnectiveDerivedEquivalence
