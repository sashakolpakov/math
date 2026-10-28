import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Cocycle Homology -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CocycleHomology

noncomputable section

/-! Explicit cochain boundaries give homotopies and equal homology maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

variable (R : Type) [CommRing R]
  {P Q : CochainComplex (ModuleCat.{0} R) ℤ} {a : ℤ}

def homotopy (z w : Cocycle P Q a) (β : Cochain P Q (a - 1))
    (h : z.1 = w.1 + δ (a - 1) a β) :
    Homotopy (Cocycle.homOf (z.rightShift a 0 (zero_add a)))
      (Cocycle.homOf (w.rightShift a 0 (zero_add a))) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨a.negOnePow • β.rightShift a (-1) (by omega), by
      simp only [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.rightShift_coe]
      rw [h]
      simp [Cochain.δ_rightShift _ _ _ _ _ _ (zero_add a), smul_smul, add_comm]⟩

theorem homologyMap_eq (z w : Cocycle P Q a) (β : Cochain P Q (a - 1))
    (h : z.1 = w.1 + δ (a - 1) a β) (n : ℤ) :
    HomologicalComplex.homologyMap (Cocycle.homOf (z.rightShift a 0 (zero_add a))) n =
      HomologicalComplex.homologyMap (Cocycle.homOf (w.rightShift a 0 (zero_add a))) n :=
  (homotopy R z w β h).homologyMap_eq n

def map (z : Cocycle P Q a) (n m : ℤ) (h : a + n = m) :
    P.homology n ⟶ Q.homology m :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (.up ℤ) 0).shiftMap
    (Cocycle.equivHomShift.symm z) n m h

theorem map_eq (z w : Cocycle P Q a) (β : Cochain P Q (a - 1))
    (h : z.1 = w.1 + δ (a - 1) a β) (n m : ℤ) (hnm : a + n = m) :
    map R z n m hnm = map R w n m hnm := by
  unfold map CategoryTheory.Functor.shiftMap
  rw [Cocycle.equivHomShift_symm_apply, Cocycle.equivHomShift_symm_apply]
  congr 1
  exact CocycleHomology.homologyMap_eq R z w β h n

@[reassoc]
theorem precomp {S : CochainComplex (ModuleCat.{0} R) ℤ}
    (z : Cocycle P Q a) (f : S ⟶ P) (n m : ℤ) (h : a + n = m) :
    map R (z.precomp f) n m h = HomologicalComplex.homologyMap f n ≫ map R z n m h := by
  simp only [map, Cocycle.equivHomShift_symm_precomp, CategoryTheory.Functor.shiftMap_comp']
  rfl

@[reassoc]
theorem postcomp {S : CochainComplex (ModuleCat.{0} R) ℤ}
    (z : Cocycle P Q a) (f : Q ⟶ S) (n m : ℤ) (h : a + n = m) :
    map R (z.postcomp f) n m h = map R z n m h ≫ HomologicalComplex.homologyMap f m := by
  simp only [map, Cocycle.equivHomShift_symm_postcomp, CategoryTheory.Functor.shiftMap_comp]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CocycleHomology
