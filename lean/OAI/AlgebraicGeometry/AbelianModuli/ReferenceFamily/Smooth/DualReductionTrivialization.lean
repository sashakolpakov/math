import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualSpecialFiber
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualAffineProduct

/-! # Dual Reduction Trivialization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualReductionTrivialization

noncomputable section

/-! Smoothness of the deformation and its exact reduction data construct
the affine product, with no separate smoothness assumption on the fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem exists_smooth_dual_product_from_reduction
    {k A S : Type*} [CommRing k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra (DualNumber k) S] [Algebra.FormallySmooth (DualNumber k) S]
    (q : S →+* A) (hq : Function.Surjective q)
    (hker : RingHom.ker q = (Dual.TensorReduction.dualScalarReductionIdeal k).map (algebraMap (DualNumber k) S))
    (hbase : ∀ c : DualNumber k, q (algebraMap (DualNumber k) S c) = algebraMap k A c.fst) :
    ∃ f : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A), ∀ s, Dual.TensorReduction.dualTensorReduction k A (f s) = q s := by
  have : Algebra.FormallySmooth k A := DualSpecialFiber.formallySmooth_dual_specialFiber q hq hker hbase
  exact DualProductComparison.exists_smooth_dual_product_comparison q hq hker hbase

theorem exists_smooth_dual_affine_product_from_reduction
    {k A S : Type} [CommRing k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra (DualNumber k) S] [Algebra.FormallySmooth (DualNumber k) S]
    (q : S →+* A) (hq : Function.Surjective q)
    (hker : RingHom.ker q = (Dual.TensorReduction.dualScalarReductionIdeal k).map (algebraMap (DualNumber k) S))
    (hbase : ∀ c : DualNumber k, q (algebraMap (DualNumber k) S c) = algebraMap k A c.fst) :
    ∃ e : EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) S ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))).obj (EtaleSplittingAt.EtaleSplitting.affineOver k A),
      Spec.map (CommRingCat.ofHom q) ≫ e.hom.left =
        Spec.map (CommRingCat.ofHom (Dual.TensorReduction.dualTensorReduction k A).toRingHom) ≫
          (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k A (DualNumber k)).hom.left := by
  have : Algebra.FormallySmooth k A := DualSpecialFiber.formallySmooth_dual_specialFiber q hq hker hbase
  exact DualAffineProduct.exists_smooth_dual_affine_product q hq hker hbase

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualReductionTrivialization
