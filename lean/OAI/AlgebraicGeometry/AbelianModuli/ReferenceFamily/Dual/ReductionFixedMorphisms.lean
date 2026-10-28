import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualOpenFactorization

/-! # Reduction Fixed Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionFixedMorphisms

noncomputable section

section

/-! Identity on the actual special fiber fixes every morphism factoring
through the closed base reduction, independently of fiber coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem dualReduction_identity_fixes_map (k : Type) [Field k]
    {X : Over (Spec (.of (DualNumber k)))} (f : X ⟶ X)
    (hf : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f =
      𝟙 ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X))
    (Z : Over (Spec (.of k))) (i : Z.left ⟶ X.left)
    (hi : i ≫ X.hom = Z.hom ≫ Smooth.AffineDualProduct.dualBaseReduction k) : i ≫ f.left = i := by
  let l : Z.left ⟶ ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X).left :=
    pullback.lift i Z.hom hi
  have hl : l ≫ VaryingDualReduction.dualFamilyReduction k X = i := pullback.lift_fst _ _ _
  have hh := congrArg Over.Hom.left hf
  change ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f).left = 𝟙 _ at hh
  have ht : VaryingDualReduction.dualFamilyReduction k X ≫ f.left = VaryingDualReduction.dualFamilyReduction k X :=
    (VaryingDualOpenFactorization.dualFamilyReduction_natural k f).trans
      ((congrArg (fun q => q ≫ VaryingDualReduction.dualFamilyReduction k X) hh).trans (Category.id_comp _))
  calc
    i ≫ f.left = (l ≫ VaryingDualReduction.dualFamilyReduction k X) ≫ f.left := congrArg (fun q => q ≫ f.left) hl.symm
    _ = l ≫ (VaryingDualReduction.dualFamilyReduction k X ≫ f.left) := Category.assoc _ _ _
    _ = l ≫ VaryingDualReduction.dualFamilyReduction k X := congrArg (fun q => l ≫ q) ht
    _ = i := hl

end

/-! Identity on the actual special fiber is equivalent to fixing its
actual closed immersion. This also detects maps built in affine coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem dualReduction_map_identity_iff (k : Type) [Field k]
    {X : Over (Spec (.of (DualNumber k)))} (f : X ⟶ X) :
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).map f = 𝟙 _ ↔
      VaryingDualReduction.dualFamilyReduction k X ≫ f.left = VaryingDualReduction.dualFamilyReduction k X := by
  constructor
  · intro h
    have hh := congrArg Over.Hom.left h
    exact (VaryingDualOpenFactorization.dualFamilyReduction_natural k f).trans
      ((congrArg (fun q => q ≫ VaryingDualReduction.dualFamilyReduction k X) hh).trans (Category.id_comp _))
  · intro h
    have := VaryingDualReduction.dualFamilyReduction_closed k X
    have : Mono (VaryingDualReduction.dualFamilyReduction k X) := inferInstance
    apply Over.OverMorphism.ext
    apply (cancel_mono (VaryingDualReduction.dualFamilyReduction k X)).mp
    exact (VaryingDualOpenFactorization.dualFamilyReduction_natural k f).symm.trans (h.trans (Category.id_comp _).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionFixedMorphisms
