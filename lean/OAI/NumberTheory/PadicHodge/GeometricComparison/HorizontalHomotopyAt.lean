import OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.HomologicalBicomplex

/-! # Horizontal Homotopy At -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HorizontalHomotopyAt.HorizontalHomotopyRows

noncomputable section

/-! A horizontal homotopy equivalence of actual complexes supplies exact
augmented rows with the original degree-zero component. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
  (M : CochainComplex A ℕ) (H : HomologicalComplex₂ A (.up ℕ) (.up ℕ))
  (e : HomotopyEquiv ((CochainComplex.single₀ (CochainComplex A ℕ)).obj M) H)

def sourceIso (q : ℕ) :
    (((HomologicalComplex.eval A (.up ℕ) q).mapHomologicalComplex (.up ℕ)).obj
      ((CochainComplex.single₀ (CochainComplex A ℕ)).obj M)) ≅
    (CochainComplex.single₀ A).obj (M.X q) :=
  (HomologicalComplex.singleMapHomologicalComplex (HomologicalComplex.eval A (.up ℕ) q) (.up ℕ) 0).app M

theorem sourceIso_inv_zero (q : ℕ) : (sourceIso M q).inv.f 0 = 𝟙 (M.X q) := by
  change ((HomologicalComplex.singleMapHomologicalComplex (HomologicalComplex.eval A (.up ℕ) q)
    (.up ℕ) 0).inv.app M).f 0 = _
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
  change 𝟙 _ ≫ (HomologicalComplex.eval A (.up ℕ) q).map (𝟙 M) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

def rowHomotopyEquiv (q : ℕ) : HomotopyEquiv ((CochainComplex.single₀ A).obj (M.X q)) (H.flip.X q) :=
  (HomotopyEquiv.ofIso (sourceIso M q).symm).trans
    ((HomologicalComplex.eval A (.up ℕ) q).mapHomotopyEquiv e)

theorem row_zero (q : ℕ) : (rowHomotopyEquiv M H e q).hom.f 0 = (e.hom.f 0).f q := by
  change (sourceIso M q).inv.f 0 ≫ (e.hom.f 0).f q = _
  rw [sourceIso_inv_zero]
  exact Category.id_comp _

include e in
theorem exactAt (q r : ℕ) : (H.flip.X q).ExactAt (r + 1) := by
  let := (rowHomotopyEquiv M H e q).quasiIso_hom
  exact (exactAt_iff_of_quasiIsoAt (rowHomotopyEquiv M H e q).hom (r + 1)).mp
    (CochainComplex.exactAt_succ_single_obj (M.X q) r)

theorem mono (q : ℕ) : Mono ((e.hom.f 0).f q) := by
  have h := (AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion.quasiIsoAt_zero_iff
    (rowHomotopyEquiv M H e q).hom (by simp; rfl)).mp
      (inferInstanceAs (QuasiIsoAt (rowHomotopyEquiv M H e q).hom 0))
  rw [row_zero] at h
  exact h.2

theorem cocycle (q : ℕ) : (e.hom.f 0).f q ≫ (H.flip.X q).d 0 1 = 0 := by
  have h := (rowHomotopyEquiv M H e q).hom.comm 0 1
  have hz : ((CochainComplex.single₀ A).obj (M.X q)).d 0 1 = 0 := by simp; rfl
  rw [hz, zero_comp, row_zero] at h
  exact h

theorem exactAugmentation (q : ℕ) :
    (ShortComplex.mk ((e.hom.f 0).f q) ((H.flip.X q).d 0 1) (cocycle M H e q)).Exact := by
  have h := (AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion.quasiIsoAt_zero_iff
    (rowHomotopyEquiv M H e q).hom (by simp; rfl)).mp
      (inferInstanceAs (QuasiIsoAt (rowHomotopyEquiv M H e q).hom 0))
  have hh := h.1
  simp only [AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion.initialShort, row_zero] at hh
  exact hh

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HorizontalHomotopyAt.HorizontalHomotopyRows
