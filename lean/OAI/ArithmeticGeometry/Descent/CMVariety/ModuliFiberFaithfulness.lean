import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli

/-! # Moduli Fiber Faithfulness -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-!
Actual enhanced fibers recover the classifying morphism once the arithmetic
base morphism is fixed. This is proved from the represented concrete
presheaf and the previously constructed universal family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem StandardModuli.Abelian.ArithmeticAbelianModuli.morphism_eq_of_enhanced_fiber_iso (M : StandardModuli.Abelian.ArithmeticAbelianModuli)
    {T : Scheme} (p q : T ⟶ M.space)
    (hbase : p ≫ M.parameter.hom = q ≫ M.parameter.hom)
    (hiso : Nonempty (ModuliObjects.Abelian.EnhancedAbelianIso (M.universal.pullback p) (M.universal.pullback q))) : p = q := by
  let T' := Over.mk (p ≫ M.parameter.hom)
  let p' : T' ⟶ M.parameter := Over.homMk p rfl
  let q' : T' ⟶ M.parameter := Over.homMk q hbase.symm
  have hclass : (M.universal.pullback p'.left).classOf = (M.universal.pullback q'.left).classOf :=
    (ModuliObjects.Abelian.EnhancedAbelianData.classOf_eq_iff _ _).mpr hiso
  rw [M.universal_pullback_class, M.universal_pullback_class] at hclass
  have heq : p' = q' := M.represents.homEquiv.injective (Subtype.ext hclass)
  exact congrArg Over.Hom.left heq

end

end OAI.ArithmeticGeometry.Descent.CMVariety
