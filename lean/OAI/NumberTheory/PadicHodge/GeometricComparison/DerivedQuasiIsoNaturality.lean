import OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiHom
import OAI.NumberTheory.PadicHodge.GeometricComparison.InverseHom

/-! # Derived Quasi Iso Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiIsoNaturality.DerivedQuasiIsoHom

noncomputable section

/-! The actual derived quasi-isomorphism comparison is natural, including the Hodge-inclusion squares. -/

open _root_.CategoryTheory

universe u v w z

variable (R : Type z) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [Linear R C] (A : C)
  {K L K' L' : CochainComplex C ℤ} (f : K ⟶ L) (g : K' ⟶ L')
  [QuasiIso f] [QuasiIso g] (a : K ⟶ K') (b : L ⟶ L') (h : f ≫ b = a ≫ g)

include h in
theorem naturality (n : ℤ)
    (x : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :
    DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A g n (x ≫ (DerivedCategory.Q.map b)⟦n⟧') =
      DerivedQuasiHom.DerivedQuasiIsoHom.equiv R A f n x ≫ (DerivedCategory.Q.map a)⟦n⟧' := by
  let H := DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory C) n
  have hs : H.map f ≫ H.map b = H.map a ≫ H.map g :=
    (H.map_comp f b).symm.trans ((congrArg H.map h).trans (H.map_comp a g))
  exact InverseHom.InverseHomCongr.naturality R
    ((shiftFunctor (DerivedCategory C) n).mapIso (asIso (DerivedCategory.Q.map f)))
    ((shiftFunctor (DerivedCategory C) n).mapIso (asIso (DerivedCategory.Q.map g)))
    (H.map a) (H.map b) hs x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DerivedQuasiIsoNaturality.DerivedQuasiIsoHom
