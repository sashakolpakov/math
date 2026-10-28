import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualReductionTrivialization

/-! # Canonical Dual Special Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualSpecialFiber

noncomputable section

/-! The canonical special fiber of a smooth affine dual-number algebra
has a constructed product trivialization retaining its quotient map. -/

open scoped TensorProduct

variable (k S : Type*) [CommRing k] [CommRing S] [Algebra (DualNumber k) S]

abbrev dualSpecialFiberIdeal : Ideal S :=
  (Dual.TensorReduction.dualScalarReductionIdeal k).map (algebraMap (DualNumber k) S)

abbrev dualSpecialFiber := S ⧸ dualSpecialFiberIdeal k S

variable [Algebra k S] [IsScalarTower k (DualNumber k) S]

theorem dualSpecialFiber_quotient_base (c : DualNumber k) :
    Ideal.Quotient.mk (dualSpecialFiberIdeal k S) (algebraMap (DualNumber k) S c) =
      algebraMap k (dualSpecialFiber k S) c.fst := by
  have hr : c - algebraMap k (DualNumber k) c.fst ∈ Dual.TensorReduction.dualScalarReductionIdeal k := by
    change c.fst - c.fst = 0
    exact sub_self _
  have hm := Ideal.mem_map_of_mem (algebraMap (DualNumber k) S) hr
  rw [map_sub, ← IsScalarTower.algebraMap_apply k (DualNumber k) S] at hm
  change Ideal.Quotient.mk (dualSpecialFiberIdeal k S) (algebraMap (DualNumber k) S c) =
    Ideal.Quotient.mk (dualSpecialFiberIdeal k S) (algebraMap k S c.fst)
  exact Ideal.Quotient.eq.mpr hm

variable [Algebra.FormallySmooth (DualNumber k) S]

theorem formallySmooth_dualSpecialFiber : Algebra.FormallySmooth k (dualSpecialFiber k S) :=
  Smooth.DualSpecialFiber.formallySmooth_dual_specialFiber (Ideal.Quotient.mk (dualSpecialFiberIdeal k S))
    Ideal.Quotient.mk_surjective Ideal.mk_ker (dualSpecialFiber_quotient_base k S)

theorem exists_smooth_dual_canonical_product :
    ∃ f : S ≃ₐ[DualNumber k] (DualNumber k ⊗[k] dualSpecialFiber k S),
      ∀ s, Dual.TensorReduction.dualTensorReduction k (dualSpecialFiber k S) (f s) =
        Ideal.Quotient.mk (dualSpecialFiberIdeal k S) s :=
  Smooth.DualReductionTrivialization.exists_smooth_dual_product_from_reduction (Ideal.Quotient.mk (dualSpecialFiberIdeal k S))
    Ideal.Quotient.mk_surjective Ideal.mk_ker (dualSpecialFiber_quotient_base k S)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualSpecialFiber
