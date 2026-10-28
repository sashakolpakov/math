import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicSheafResolution
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Sheaf Complex Global Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafComplexGlobalSections.IntrinsicCech

noncomputable section

/-! An exact nonnegative complex of acyclic additive sheaves remains exact
on global sections. A zero next term makes the corresponding section map surjective. -/
open scoped ZeroObject
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false in
theorem acyclic_sheafComplex_sections_exact
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) (hK : K.Acyclic)
    (hH : ∀ i q, Subsingleton (CategoryTheory.Sheaf.H (K.X i) (q + 1)))
    (n : ℕ) (x : (K.X (n + 1)).obj.obj (op ⊤))
    (hx : (K.d (n + 1) (n + 2)).hom.app (op ⊤) x = 0) :
    ∃ y : (K.X n).obj.obj (op ⊤), (K.d n (n + 1)).hom.app (op ⊤) y = x := by
  let e : (0 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⟶ K.X 0 := 0
  have w : e ≫ K.d 0 1 = 0 := zero_comp
  have hs : (K.sc' 0 0 1).Exact :=
    (K.exactAt_iff' 0 0 1 (by simp) (by simp)).mp (hK 0)
  have : Mono (K.d 0 1) := hs.mono_g (K.shape 0 0 (by simp))
  have haug : (ShortComplex.mk e (K.d 0 1) w).Exact :=
    ((ShortComplex.mk e (K.d 0 1) w).exact_iff_mono rfl).mpr inferInstance
  have hpos (i : ℕ) : (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K i).Exact :=
    (K.exactAt_iff' i (i + 1) (i + 2) (by simp) (by simp)).mp (hK (i + 1))
  exact AcyclicSheafResolution.IntrinsicCech.acyclicResolution_sections_exact_succ K e w haug hpos
    (fun q => CategoryTheory.Sheaf.subsingleton_H_of_isZero (isZero_zero _) (q + 1)) hH n x hx

theorem acyclic_sheafComplex_last_sections_surjective
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ) (hK : K.Acyclic)
    (hH : ∀ i q, Subsingleton (CategoryTheory.Sheaf.H (K.X i) (q + 1)))
    (n : ℕ) (hnext : IsZero (K.X (n + 2))) :
    Function.Surjective ((K.d n (n + 1)).hom.app (op (⊤ : Opens X))) := by
  intro x
  apply acyclic_sheafComplex_sections_exact K hK hH n x
  rw [hnext.eq_of_tgt (K.d (n + 1) (n + 2)) 0]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafComplexGlobalSections.IntrinsicCech
