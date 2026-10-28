import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.CechTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.TensorBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Affine Cech Tensor Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineCechTensorIsomorphism

noncomputable section

/-! On a finite affine frame cover of a line bundle, the canonical Cech tensor map for arbitrary affine base change is invertible. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [X.IsSeparated]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
variable {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
variable (ha : ∀ i, IsAffineOpen (U i))
variable (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme))

include ha he in
theorem geometricCechTensorPushforwardMap_isIso : IsIso (Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U) := by
  apply OrderedCech.TensorIsomorphism.CechTensorComparison.map_isIso
  intro q i
  let V : X.Opens := ∏ᶜ fun k => U (i.1 k)
  have hV : IsAffineOpen V := Affine.CechIntersections.affine_cechIntersection U ha q i.1
  have hle : V ≤ U (i.1 0) := leOfHom (Pi.π (fun k => U (i.1 k)) 0)
  have hframe := L.frameRestrict hle (he (i.1 0)).some
  exact AffineOpen.TensorBaseChange.affineFrame_moduleTensorComparison_isIso H L.sheaf V hV hframe

include ha he in
theorem geometricCechTensorMap_isIso : IsIso (Geometric.CechTensorComparison.geometricCechTensorMap H L.sheaf U) := by
  have := geometricCechTensorPushforwardMap_isIso H L U ha he
  change IsIso (Geometric.CechTensorComparison.geometricCechTensorPushforwardMap H L.sheaf U ≫ _)
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineCechTensorIsomorphism
