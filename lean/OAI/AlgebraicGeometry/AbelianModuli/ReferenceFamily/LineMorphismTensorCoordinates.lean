import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.TensorTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.LineMorphismEquiv

/-! # Line Morphism Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineMorphismTensorCoordinates

noncomputable section

/-! Tensoring an actual line-sheaf morphism with an identity preserves
its literal coefficient in the induced common tensor frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {M N H : X.Modules}

theorem lineMorphismCoefficient_tensor (f : M ⟶ N) (U W : X.Opens) (hW : W ≤ U)
    (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (g : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (h : H.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    LineFrameAtlas.lineMorphismCoefficient (HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H)) (Local.TensorTransitions.localTensorFrame U e h) (Local.TensorTransitions.localTensorFrame U g h)
      W hW hW = LineFrameAtlas.lineMorphismCoefficient f ⟨U, e⟩ ⟨U, g⟩ W hW hW := by
  let r : LineFrameAtlas.LocalLineFrame M := ⟨U, e⟩
  let s : LineFrameAtlas.LocalLineFrame N := ⟨U, g⟩
  let t : LineFrameAtlas.LocalLineFrame H := ⟨U, h⟩
  let R := Local.TensorTransitions.localTensorFrame U e h
  let S := Local.TensorTransitions.localTensorFrame U g h
  let x := (r.coordinates W hW).symm 1
  let y := (t.coordinates W hW).symm 1
  have hR : (R.coordinates W hW).symm 1 = (SheafTensorMaps.tensorBilinear M H).app W x y := by
    apply (R.coordinates W hW).injective
    rw [LinearEquiv.apply_symm_apply]
    have hxy := Tensor.FrameCoordinates.tensorFrameOnOpen_apply M H U e h W hW x y
    change _ = (r.coordinates W hW x) * (t.coordinates W hW y) at hxy
    exact (hxy.trans (by simp only [x, y, LinearEquiv.apply_symm_apply, one_mul])).symm
  have hf := SheafTensorMaps.sheafTensorMap_apply f (𝟙 H) W x y
  change (HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H)).app W ((SheafTensorMaps.tensorBilinear M H).app W x y) =
    (SheafTensorMaps.tensorBilinear N H).app W (f.app W x) y at hf
  change S.coordinates W hW ((HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H)).app W ((R.coordinates W hW).symm 1)) =
    s.coordinates W hW (f.app W x)
  rw [hR]
  have hS := Tensor.FrameCoordinates.tensorFrameOnOpen_apply N H U g h W hW (f.app W x) y
  change S.coordinates W hW ((SheafTensorMaps.tensorBilinear N H).app W (f.app W x) y) =
    (s.coordinates W hW (f.app W x)) * (t.coordinates W hW y) at hS
  exact (congrArg (S.coordinates W hW) hf).trans
    (hS.trans (by rw [show t.coordinates W hW y = 1 from LinearEquiv.apply_symm_apply _ _, mul_one]))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineMorphismTensorCoordinates
