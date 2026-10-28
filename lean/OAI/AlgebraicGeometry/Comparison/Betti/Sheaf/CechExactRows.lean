import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechAugmentation
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Cech Exact Rows -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechExactRows

noncomputable section

/-! Every augmented row of the actual sheaf Čech bicomplex is exact on an open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
  (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ)

include hU

theorem sheafCechComplexAugmentation_mono (q : ℕ) :
    Mono (CechAugmentation.sheafCechComplexAugmentation U K q) :=
  SheafCohomology.Cech.Resolution.TopCat.Sheaf.cechAugmentation_mono (K.X q) U hU

theorem sheafCechComplexAugmentation_exact (q : ℕ) :
    (ShortComplex.mk (CechAugmentation.sheafCechComplexAugmentation U K q)
      (((CechAugmentation.sheafCechBicomplex U K).X q).d 0 1)
      (CechAugmentation.sheafCechComplexAugmentation_comp_d U K q)).Exact := by
  change (ShortComplex.mk (SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation (K.X q) U)
    ((SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex (K.X q) U).d 0 1) _).Exact
  have h := SheafCohomology.Cech.ZeroExact.TopCat.Sheaf.cechAugmentedShortComplex_exact (K.X q) U hU
  convert h using 1
  congr 1

theorem sheafCechBicomplex_row_exact (q n : ℕ) :
    ((CechAugmentation.sheafCechBicomplex U K).X q).ExactAt (n + 1) := by
  let J := SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex (K.X q) U
  change J.ExactAt (n + 1)
  rw [J.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
  change (ShortComplex.mk (J.d n (n + 1)) (J.d (n + 1) (n + 2)) _).Exact
  dsimp only [J]
  have h := SheafCohomology.Cech.PositiveExact.TopCat.Sheaf.cechShortComplex_exact (K.X q) U hU n
  convert h using 1
  congr 1
  · exact SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex_d (K.X q) U n
  · exact SheafCohomology.Cech.SheafComplex.TopCat.Sheaf.cechComplex_d (K.X q) U (n + 1)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechExactRows
