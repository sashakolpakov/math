import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.AlgebraAutomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.DerivationLaws
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorDerivationGauges

/-! # Chart Gauge Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.ChartGaugeCancellation

noncomputable section

section

/-! Every derivation constructs an actual affine product automorphism
over the full dual-number base that fixes the actual special fiber.
Together with coefficient extraction this gives an exact equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of k))) [IsAffine X.left]

def affineProductDerivationGauge
    (d : Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)) :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X :=
  AlgebraAutomorphisms.affineProductAlgebraAutomorphism k X (Dual.TensorDerivationGauges.dualTensorDerivationGauge d)

theorem affineProductDerivationGauge_fiberIdentity
    (d : Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)) :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (affineProductDerivationGauge k X d).hom = 𝟙 _ :=
  AlgebraAutomorphisms.affineProductAlgebraAutomorphism_fiberIdentity k X (Dual.TensorDerivationGauges.dualTensorDerivationGauge d)
    (Dual.TensorDerivationGauges.dualTensorDerivationGauge_reduction d)

theorem affineProductDerivationGauge_derivation
    (d : Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X)) :
    TransitionDerivation.affineProductTransitionDerivation k X (affineProductDerivationGauge k X d)
      (affineProductDerivationGauge_fiberIdentity k X d) = d := by
  unfold TransitionDerivation.affineProductTransitionDerivation
  exact (Dual.TransitionDerivationFaithfulness.dualTensorTransitionDerivation_congr _ _ _ (Dual.TensorDerivationGauges.dualTensorDerivationGauge_reduction d)
    (AlgebraAutomorphisms.affineProductAlgebraAutomorphism_algebra k X (Dual.TensorDerivationGauges.dualTensorDerivationGauge d))).trans
    (Dual.TensorDerivationGauges.dualTensorDerivationGauge_derivation d)

def affineProductInfinitesimalAutomorphismEquiv :
    {e : (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X //
        (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map e.hom = 𝟙 _} ≃
      Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) where
  toFun e := TransitionDerivation.affineProductTransitionDerivation k X e.1 e.2
  invFun d := ⟨affineProductDerivationGauge k X d, affineProductDerivationGauge_fiberIdentity k X d⟩
  left_inv e := Subtype.ext (DerivationLaws.affineProductTransitionDerivation_faithful k X _ _ _ _
    (affineProductDerivationGauge_derivation k X (TransitionDerivation.affineProductTransitionDerivation k X e.1 e.2)))
  right_inv := affineProductDerivationGauge_derivation k X

end

/-! A derivation coboundary makes the adjusted actual scheme product
charts literally equal. No abstract chart or global product is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [Field k] (X : Over (Spec (.of k))) [IsAffine X.left]
    {Z : Over (Spec (.of (DualNumber k)))}

theorem affineProductChartGauge_cancellation
    (u v : Z ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj X)
    (h : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map (u.symm ≪≫ v).hom = 𝟙 _)
    (a b : Derivation k (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X) (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k X))
    (hd : TransitionDerivation.affineProductTransitionDerivation k X (u.symm ≪≫ v) h = a - b) :
    u ≪≫ affineProductDerivationGauge k X a = v ≪≫ affineProductDerivationGauge k X b := by
  let t := u.symm ≪≫ v
  let g := affineProductDerivationGauge k X b
  let G := Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)
  have hg : G.map g.hom = 𝟙 _ := affineProductDerivationGauge_fiberIdentity k X b
  have ht : G.map (t ≪≫ g).hom = 𝟙 _ := by
    change G.map (t.hom ≫ g.hom) = _
    rw [G.map_comp, h, hg, Category.id_comp]
  have hd' : TransitionDerivation.affineProductTransitionDerivation k X (t ≪≫ g) ht = a := by
    calc
      TransitionDerivation.affineProductTransitionDerivation k X (t ≪≫ g) ht =
          TransitionDerivation.affineProductTransitionDerivation k X t h + TransitionDerivation.affineProductTransitionDerivation k X g hg :=
        DerivationLaws.affineProductTransitionDerivation_trans k X t g h hg ht
      _ = (a - b) + b := congrArg₂ (· + ·) hd (affineProductDerivationGauge_derivation k X b)
      _ = a := sub_add_cancel a b
  have he := DerivationLaws.affineProductTransitionDerivation_faithful k X (t ≪≫ g)
    (affineProductDerivationGauge k X a) ht (affineProductDerivationGauge_fiberIdentity k X a)
    (hd'.trans (affineProductDerivationGauge_derivation k X a).symm)
  have hh := congrArg (fun e => u.hom ≫ e.hom) he
  apply Iso.ext
  change u.hom ≫ (u.inv ≫ v.hom) ≫ g.hom = u.hom ≫ (affineProductDerivationGauge k X a).hom at hh
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hh
  exact hh.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AffineProduct.ChartGaugeCancellation
