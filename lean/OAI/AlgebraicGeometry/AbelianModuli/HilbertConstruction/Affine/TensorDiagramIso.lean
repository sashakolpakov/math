import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraTensorFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorIsoNaturality

/-! # Tensor Diagram Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorDiagramIso

noncomputable section

/-! A whole tensor coordinate diagram is naturally isomorphic to the actual base-changed affine scheme diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
variable {J : Type v} [Category.{w} J] (F : J ⥤ Over (Spec (.of C)))
variable [∀ i, IsAffine (F.obj i).left]

abbrev affineTensorDiagram : J ⥤ Over (Spec (.of R)) :=
  (CoordinateFunctor.affineCoordinateFunctor C F ⋙ AlgebraTensorFunctor.algebraTensorFunctor C R).rightOp ⋙ algSpec (.of R)

def affineTensorDiagramIso : affineTensorDiagram C R F ≅
    F ⋙ Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R))) :=
  NatIso.ofComponents (fun i => TensorOverIso.affineTensorOverIso C R (F.obj i))
    (fun h => TensorIsoNaturality.affineTensorOverIso_natural (F.map h))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorDiagramIso
