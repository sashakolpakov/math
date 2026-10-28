import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.ConcreteTriviality

/-! # Symmetric Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.SymmetricRestriction

noncomputable section

/-! On the actual polarization kernel, the tensor product of a line
bundle with its inverse-argument pullback is trivial. This follows by
restricting the universal polarization family to the inverse graph. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (CommRingCat.of K))}

theorem polarizationFamilyClass_graph (a b : T ⟶ A) :
    SchemePointPicardPairing.Construction.additivePicardPullback (lift (𝟙 T) b).left (Polarization.Family.Construction.polarizationFamilyClass A L a) =
      SchemePointPicardPairing.Construction.schemePointPicardPairing A L T (Additive.ofMul a) (Additive.ofMul b) := by
  unfold Polarization.Family.Construction.polarizationFamilyClass
  rw [SchemePointPicardPairing.Construction.schemePointPicardPairing_pullback]
  simp only [toMul_ofMul, lift_fst_assoc, Category.id_comp, lift_snd]

theorem polarizationKernel_symmetricRestriction_trivial [IsLocallyNoetherian T.left]
    (a : T ⟶ A) (h : Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    Nonempty (((L.pullback a.left).tensor (L.pullback (a⁻¹).left)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left) := by
  have hz := ConcreteTriviality.Construction.polarizationFamilyClass_zero_of_relative_zero A L a h
  have hb : SchemePointPicardPairing.Construction.schemePointPicardPairing A L T (Additive.ofMul a) (Additive.ofMul a⁻¹) = 0 := by
    rw [← polarizationFamilyClass_graph A L a a⁻¹, hz, map_zero]
  rw [SchemePointPicardPairing.Construction.schemePointPicardPairing_apply] at hb
  change SchemePointPicardPairing.Construction.schemePointLineBundleClass A L T (Additive.ofMul (a * a⁻¹)) -
    SchemePointPicardPairing.Construction.schemePointLineBundleClass A L T (Additive.ofMul a) -
      SchemePointPicardPairing.Construction.schemePointLineBundleClass A L T (Additive.ofMul a⁻¹) = 0 at hb
  rw [mul_inv_cancel] at hb
  change SchemePointPicardPairing.Construction.schemePointLineBundleClass A L T 0 - _ - _ = 0 at hb
  rw [SchemePointPicardPairing.Construction.schemePointLineBundleClass_zero] at hb
  have he : SchemePointPicardPairing.Construction.schemePointLineBundleClass A L T (Additive.ofMul a) +
      SchemePointPicardPairing.Construction.schemePointLineBundleClass A L T (Additive.ofMul a⁻¹) = 0 := by
    simpa only [sub_eq_add_neg, zero_add, ← neg_add, neg_eq_zero] using hb
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((L.pullback a.left).tensor (L.pullback (a⁻¹).left)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) := congrArg Additive.toMul he
  exact Quotient.exact hc

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.SymmetricRestriction
