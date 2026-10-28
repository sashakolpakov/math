import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AlgebraFunctorRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagramIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeTensorDiagramIso

/-! # Scheme Functor Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

noncomputable section

/-! Descended smooth algebra functors give smooth affine scheme diagrams with natural base-change recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R] {J : Type v} [Category.{w} J]
variable {A : Jᵒᵖ ⥤ CommAlgCat.{u} R} (M : AlgebraFunctorModel.SmoothAlgebraFunctorModel R A)

abbrev AlgebraFunctorModel.SmoothAlgebraFunctorModel.schemeFunctor : J ⥤ Over (Spec (.of M.coefficients)) :=
  AlgebraSchemeDiagrams.algebraSchemeDiagram M.coefficients M.algebraFunctor

instance AlgebraFunctorModel.SmoothAlgebraFunctorModel.schemeFunctor_smooth (i : J) : Smooth (M.schemeFunctor.obj i).hom := by
  have (j : Jᵒᵖ) : Algebra.Smooth M.coefficients (M.algebraFunctor.obj j) := M.smooth j
  exact AlgebraSchemeDiagrams.algebraSchemeDiagram_smooth _ _ i

instance AlgebraFunctorModel.SmoothAlgebraFunctorModel.schemeFunctor_open {i j : J} (f : i ⟶ j) :
    IsOpenImmersion (M.schemeFunctor.map f).left := M.arrow_open ⟨Opposite.op j, Opposite.op i, f.op⟩

def AlgebraFunctorModel.SmoothAlgebraFunctorModel.schemeRecoveryIso :
    M.schemeFunctor ⋙ Over.pullback (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)) ≅
      AlgebraSchemeDiagrams.algebraSchemeDiagram R A :=
  (SchemeTensorDiagramIso.algebraSchemeTensorDiagramIso M.coefficients R M.algebraFunctor).symm ≪≫
    AlgebraSchemeDiagramIsomorphisms.algebraSchemeDiagramIso R M.recoveryIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth
