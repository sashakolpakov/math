import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingDerivedCocycle

/-! # Cocycle Composition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CocycleComposition

noncomputable section

/-! Explicit degree-one cocycle composition and its actual shifted morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {A B K : CochainComplex C ℤ}

def cocycleOneComp (a : Cocycle A B 1) (b : Cocycle B K 1) : Cocycle A K 2 :=
  Cocycle.mk (a.val.comp b.val rfl) 3 rfl (by
    rw [δ_comp a.val b.val (show (1 : ℤ) + 1 = 2 from rfl) 2 2 3 rfl rfl rfl,
      Cocycle.δ_eq_zero, Cocycle.δ_eq_zero, Cochain.zero_comp, Cochain.comp_zero,
      smul_zero, add_zero])

theorem cocycleShiftHom_f {n : ℤ} (z : Cocycle A K n) (p : ℤ) :
    (Cocycle.equivHomShift.symm z).f p = z.val.v p (p + n) rfl := by
  change z.val.v p (p + n) rfl ≫ (K.shiftFunctorObjXIso n p (p + n) rfl).inv = _
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso_refl,
    Iso.refl_inv, Category.comp_id]

theorem cocycleOneComp_shiftHom (a : Cocycle A B 1) (b : Cocycle B K 1) :
    Cocycle.equivHomShift.symm (cocycleOneComp a b) =
      ShiftedHom.comp (Cocycle.equivHomShift.symm a) (Cocycle.equivHomShift.symm b) (show (1 : ℤ) + 1 = 2 from rfl) := by
  apply HomologicalComplex.Hom.ext
  funext p
  rw [cocycleShiftHom_f]
  change (a.val.comp b.val rfl).v p (p + 2) rfl = _
  rw [Cochain.comp_v _ _ rfl p (p + 1) (p + 2) rfl (by omega)]
  simp only [ShiftedHom.comp, HomologicalComplex.comp_f, shiftFunctor_map_f',
    cocycleShiftHom_f, shiftFunctorAdd'_inv_app_f']
  rw [Cochain.v_comp_XIsoOfEq_hom]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CocycleComposition
