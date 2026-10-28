import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Embedding Cartesian Kernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingCartesianKernels

noncomputable section

/-! A Cartesian square of closed embeddings identifies the inverse-image ideal sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem closedEmbedding_ker_of_isPullback
    {ZX ZY X Y : Scheme.{u}} (iX : ZX ⟶ X) (iY : ZY ⟶ Y) (q : ZX ⟶ ZY) (f : X ⟶ Y)
    [IsClosedImmersion iY] (h : IsPullback iX q f iY) : iX.ker = iY.ker.comap f := by
  calc
    iX.ker = (h.isoPullback.hom ≫ pullback.fst f iY).ker := congrArg (fun k => k.ker) h.isoPullback_hom_fst.symm
    _ = (pullback.fst f iY).ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = iY.ker.comap f := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion iY f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingCartesianKernels
