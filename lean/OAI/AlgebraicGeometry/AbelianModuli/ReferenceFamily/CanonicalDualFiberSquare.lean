import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualSpecialFiber
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.QuotientSpecialFiber

/-! # Canonical Dual Fiber Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualFiberSquare

noncomputable section

/-! The canonical quotient fiber is the actual scheme pullback along
the original dual-number reduction, with the original coefficient base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] Dual.TensorReduction.dualScalarReductionIdeal
attribute [local irreducible] Smooth.DualSpecialFiber.dualScalarQuotientEquiv

variable (k S : Type) [CommRing k] [CommRing S]
    [Algebra (DualNumber k) S] [Algebra k S] [IsScalarTower k (DualNumber k) S]

theorem dualQuotientFiber_structure_square :
    Spec.map (CommRingCat.ofHom (algebraMap ((DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k)
      (CanonicalDualSpecialFiber.dualSpecialFiber k S))) ≫
      Spec.map (CommRingCat.ofHom (R := k) (S := (DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k)
        (Smooth.DualSpecialFiber.dualScalarQuotientEquiv k).symm.toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap k (CanonicalDualSpecialFiber.dualSpecialFiber k S))) := by
  have : IsScalarTower k ((DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k) (CanonicalDualSpecialFiber.dualSpecialFiber k S) :=
    IsScalarTower.to₁₃₄ k (DualNumber k) ((DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k) (CanonicalDualSpecialFiber.dualSpecialFiber k S)
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change (@algebraMap ((DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k) (CanonicalDualSpecialFiber.dualSpecialFiber k S)
    (Ideal.Quotient.commSemiring _) (Ideal.Quotient.semiring _) inferInstance)
      ((Smooth.DualSpecialFiber.dualScalarQuotientEquiv k).symm c) = _
  have he : (Smooth.DualSpecialFiber.dualScalarQuotientEquiv k).symm c =
      algebraMap k ((DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k) c :=
    (Smooth.DualSpecialFiber.dualScalarQuotientEquiv k).symm.commutes c
  rw [he, ← IsScalarTower.algebraMap_apply k ((DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k)
    (CanonicalDualSpecialFiber.dualSpecialFiber k S)]
  rfl

theorem dualScalarQuotient_reduction_square :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Dual.TensorReduction.dualScalarReductionIdeal k))) =
      Spec.map (CommRingCat.ofHom (R := k) (S := (DualNumber k) ⧸ Dual.TensorReduction.dualScalarReductionIdeal k)
        (Smooth.DualSpecialFiber.dualScalarQuotientEquiv k).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  apply (Smooth.DualSpecialFiber.dualScalarQuotientEquiv k).injective
  change Smooth.DualSpecialFiber.dualScalarQuotientEquiv k (Ideal.Quotient.mk (Dual.TensorReduction.dualScalarReductionIdeal k) c) =
    Smooth.DualSpecialFiber.dualScalarQuotientEquiv k ((Smooth.DualSpecialFiber.dualScalarQuotientEquiv k).symm c.fst)
  rw [AlgEquiv.apply_symm_apply]
  exact Smooth.DualSpecialFiber.dualScalarQuotientEquiv_mk k c

theorem canonical_dual_specialFiber_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (CanonicalDualSpecialFiber.dualSpecialFiberIdeal k S))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (CanonicalDualSpecialFiber.dualSpecialFiber k S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (DualNumber k) S)))
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) := by
  have h := Affine.QuotientSpecialFiber.affine_quotient_specialFiber_isPullback (DualNumber k) S (Dual.TensorReduction.dualScalarReductionIdeal k)
  refine h.of_iso (Iso.refl _) (Iso.refl _)
    (Scheme.Spec.mapIso (Smooth.DualSpecialFiber.dualScalarQuotientEquiv k).symm.toRingEquiv.toCommRingCatIso.op)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change _ = (𝟙 _) ≫ _
    rw [Category.id_comp]
    exact dualQuotientFiber_structure_square k S
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change _ ≫ (𝟙 _) = _
    rw [Category.comp_id]
    exact dualScalarQuotient_reduction_square k

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualFiberSquare
