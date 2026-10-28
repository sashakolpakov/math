import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.Coordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionFixedMorphisms
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FunctorFixedAutomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReductionEquiv

/-! # Reduction Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.ReductionIdentity

noncomputable section

/-! An actual product automorphism that is the identity on the scheme
special fiber preserves the literal tensor reduction in algebra coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [Field k] (X : Over (Spec (.of k))) [IsAffine X.left]

local instance affineProductReductionIdentity_tensorCommRing :
    CommRing (DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)

theorem affineProductAutomorphismAlgebra_reduction
    (e : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (he : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map e.hom =
      𝟙 ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj ((Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)))
    (u : DualNumber k ⊗[k] HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) :
    Dual.TensorReduction.dualTensorReduction k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (Coordinates.affineProductAutomorphismAlgebra k X e u) =
      Dual.TensorReduction.dualTensorReduction k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) u := by
  let A := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X
  let q := Dual.TensorReduction.dualTensorReduction k A
  let f := Coordinates.affineProductCoordinateAutomorphism k X e
  have hf : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f.hom =
      𝟙 ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) (DualNumber k ⊗[k] A))) :=
    FunctorFixedAutomorphisms.functor_map_conjugate_identity (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k))
      (Coordinates.affineProductCoordinates k X) e he
  have hb : Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) (DualNumber k ⊗[k] A)).hom =
        (EtaleSplittingAt.EtaleSplitting.affineOver k A).hom ≫ Smooth.AffineDualProduct.dualBaseReduction k := by
    change Spec.map (CommRingCat.ofHom q.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (DualNumber k) (DualNumber k ⊗[k] A))) =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) ≫
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (Dual.TensorReductionEquiv.dualTensorReduction_algebraMap k A)
  have hs := Dual.ReductionFixedMorphisms.dualReduction_identity_fixes_map k f.hom hf (EtaleSplittingAt.EtaleSplitting.affineOver k A)
    (Spec.map (CommRingCat.ofHom q.toRingHom)) hb
  have hspec : Spec.map (CommRingCat.ofHom (Coordinates.affineProductAutomorphismAlgebra k X e).toRingHom) =
      f.hom.left := Coordinates.affineProductAutomorphismAlgebra_spec k X e
  rw [← hspec, ← Spec.map_comp] at hs
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  exact RingHom.congr_fun hr u

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.ReductionIdentity
