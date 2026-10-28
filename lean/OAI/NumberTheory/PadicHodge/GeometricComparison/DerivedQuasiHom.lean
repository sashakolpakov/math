import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Derived Quasi Hom -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiHom.DerivedQuasiIsoHom

noncomputable section

/-! Actual quasi-isomorphisms induce linear identifications of derived coefficient cohomology. -/

open _root_.CategoryTheory

universe u v w z

variable (R : Type z) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [Linear R C]
  (A : C) {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]

def equiv (n : ℤ) :
    ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj L)⟦n⟧) ≃ₗ[R]
      ((DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  (Linear.homCongr R (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A))
    ((shiftFunctor (DerivedCategory C) n).mapIso (asIso (DerivedCategory.Q.map f)))).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiHom.DerivedQuasiIsoHom
