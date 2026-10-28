import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSchemeDiagrams
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecTensorNaturality

/-! # Scheme Tensor Diagram Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeTensorDiagramIso

noncomputable section

/-! Tensor extension of any coordinate algebra diagram represents its actual scheme base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

def algebraSchemeTensorDiagramIso (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]
    {J : Type v} [Category.{w} J] (A : Jᵒᵖ ⥤ CommAlgCat.{u} C) :
    AlgebraSchemeDiagrams.algebraSchemeDiagram D (A ⋙ AlgebraTensorFunctor.algebraTensorFunctor C D) ≅
      AlgebraSchemeDiagrams.algebraSchemeDiagram C A ⋙
        Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D))) :=
  NatIso.ofComponents (fun i => AlgebraSpecTensorIso.algebraSpecTensorIso C D (A.obj (Opposite.op i)))
    (fun h => AlgebraSpecTensorNaturality.algebraSpecTensorIso_natural (A.map h.op))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SchemeTensorDiagramIso
