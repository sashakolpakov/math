import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualProductComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt

/-! # Dual Affine Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualAffineProduct

noncomputable section

/-! A smooth affine dual-number deformation is an actual scheme product
over the dual-number base, with its prescribed special-fiber inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable {k A S : Type} [CommRing k] [CommRing A] [CommRing S]
    [Algebra k A] [Algebra (DualNumber k) S]
    [Algebra.FormallySmooth k A] [Algebra.FormallySmooth (DualNumber k) S]

local instance : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

theorem exists_smooth_dual_affine_product (q : S →+* A) (hq : Function.Surjective q)
    (hker : RingHom.ker q = (Dual.TensorReduction.dualScalarReductionIdeal k).map (algebraMap (DualNumber k) S))
    (hbase : ∀ c : DualNumber k, q (algebraMap (DualNumber k) S c) = algebraMap k A c.fst) :
    ∃ e : EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) S ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))).obj (EtaleSplittingAt.EtaleSplitting.affineOver k A),
      Spec.map (CommRingCat.ofHom q) ≫ e.hom.left =
        Spec.map (CommRingCat.ofHom (Dual.TensorReduction.dualTensorReduction k A).toRingHom) ≫
          (EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k A (DualNumber k)).hom.left := by
  obtain ⟨f, hf⟩ := DualProductComparison.exists_smooth_dual_product_comparison q hq hker hbase
  let a := EtaleSplittingAt.EtaleSplitting.affineAlgIso (DualNumber k) S f
  let b := EtaleSplittingAt.EtaleSplitting.affineBaseChangeIso k A (DualNumber k)
  let e := a.symm ≪≫ b
  have hqf : CommRingCat.ofHom q =
      CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom (Dual.TensorReduction.dualTensorReduction k A).toRingHom := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun s => (hf s).symm)
  have ha : a.hom.left ≫ a.inv.left = 𝟙 _ := congrArg Over.Hom.left a.hom_inv_id
  refine ⟨e, ?_⟩
  change Spec.map (CommRingCat.ofHom q) ≫ (a.inv.left ≫ b.hom.left) = _
  rw [hqf, Spec.map_comp]
  change (Spec.map (CommRingCat.ofHom (Dual.TensorReduction.dualTensorReduction k A).toRingHom) ≫ a.hom.left) ≫
    (a.inv.left ≫ b.hom.left) = _
  rw [Category.assoc, ← Category.assoc a.hom.left a.inv.left, ha, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualAffineProduct
