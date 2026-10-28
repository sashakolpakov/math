import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AlgebraFunctorModel

/-! # Algebra Functor Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

noncomputable section

/-! The recovered algebra functor is naturally isomorphic to the original algebra diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R] {J : Type v} [Category.{w} J]
variable {A : J ⥤ CommAlgCat.{u} R} (M : AlgebraFunctorModel.SmoothAlgebraFunctorModel R A)

def AlgebraFunctorModel.SmoothAlgebraFunctorModel.recoveryIso : A ≅ M.algebraFunctor ⋙ AlgebraTensorFunctor.algebraTensorFunctor M.coefficients R :=
  NatIso.ofComponents (fun i => CommAlgCat.isoMk (M.recovery i)) (fun {i j} f => by
    apply CommAlgCat.hom_ext
    ext x
    exact M.recovery_naturality ⟨i, j, f⟩ x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth
