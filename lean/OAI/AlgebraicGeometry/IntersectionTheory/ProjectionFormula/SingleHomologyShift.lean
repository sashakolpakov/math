import Mathlib.CategoryTheory.Shift.SingleFunctors
import Mathlib.CategoryTheory.Shift.ShiftSequence

/-! # Single Homology Shift -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingleHomologyShift

noncomputable section

/-! Compatibility between the canonical normalization of a single column
and the homology shift. This uses the native coherence laws for shifts. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [HasShift D ℤ]
  (F : SingleFunctors C D ℤ) (H : D ⥤ E) [H.ShiftSequence ℤ] (M : C)

def iso (d n k : ℤ) (h : -d + n = k) :
    (H.shift n).obj ((F.functor d).obj M) ≅ (H.shift k).obj ((F.functor 0).obj M) :=
  (H.shift n).mapIso ((F.shiftIso (-d) d 0 (neg_add_cancel d)).symm.app M) ≪≫
    (H.shiftIso (-d) n k h).app ((F.functor 0).obj M)

theorem single_composition (a d e : ℤ) (he : a + d = e) :
    (F.shiftIso a d e he).hom.app M ≫ (F.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app M =
      ((F.shiftIso (-e) e 0 (neg_add_cancel e)).inv.app M)⟦a⟧' ≫
        (shiftFunctorAdd' D (-e) a (-d) (by omega)).inv.app ((F.functor 0).obj M) := by
  rw [SingleFunctors.shiftIso_add'_inv_app F a (-e) (-d) (by omega) d e 0 he (neg_add_cancel e) M]
  rw [Iso.hom_inv_id_app_assoc]

@[reassoc]
theorem shift (a d e n m k : ℤ) (he : a + d = e) (hm : a + n = m) (hk : -d + n = k) :
    (H.shiftIso a n m hm).hom.app ((F.functor e).obj M) ≫
        (iso F H M e m k (by omega)).hom =
      (H.shift n).map ((F.shiftIso a d e he).hom.app M) ≫ (iso F H M d n k hk).hom := by
  change (H.shiftIso a n m hm).hom.app ((F.functor e).obj M) ≫
    H.shiftMap ((F.shiftIso (-e) e 0 (neg_add_cancel e)).inv.app M) m k (by omega) =
    (H.shift n).map ((F.shiftIso a d e he).hom.app M) ≫
      H.shiftMap ((F.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app M) n k hk
  rw [CategoryTheory.Functor.shiftIso_hom_app_comp_shiftMap _ _ a (-d) (by omega)]
  simp only [CategoryTheory.Functor.shiftMap, ← CategoryTheory.Functor.map_comp_assoc]
  rw [single_composition]

@[reassoc]
theorem naturality {N : C} (f : M ⟶ N) (d n k : ℤ) (h : -d + n = k) :
    (H.shift n).map ((F.functor d).map f) ≫ (iso F H N d n k h).hom =
      (iso F H M d n k h).hom ≫ (H.shift k).map ((F.functor 0).map f) := by
  have hf : (F.functor d).map f ≫ (F.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app N =
      (F.shiftIso (-d) d 0 (neg_add_cancel d)).inv.app M ≫ ((F.functor 0).map f)⟦-d⟧' :=
    (F.shiftIso (-d) d 0 (neg_add_cancel d)).inv.naturality f
  simp only [iso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  rw [← CategoryTheory.Functor.map_comp_assoc, hf, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, CategoryTheory.Functor.shiftIso_hom_naturality]

@[reassoc]
theorem shiftMap {Z : D} (a d e n m k : ℤ) (he : a + d = e) (hm : a + n = m)
    (hk : -d + n = k) (f : Z ⟶ ((F.functor e).obj M)⟦a⟧) :
    H.shiftMap f n m hm ≫ (iso F H M e m k (by omega)).hom =
      (H.shift n).map (f ≫ (F.shiftIso a d e he).hom.app M) ≫ (iso F H M d n k hk).hom := by
  rw [CategoryTheory.Functor.shiftMap, Category.assoc, SingleHomologyShift.shift F H M a d e n m k he hm hk,
    ← CategoryTheory.Functor.map_comp_assoc]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SingleHomologyShift
