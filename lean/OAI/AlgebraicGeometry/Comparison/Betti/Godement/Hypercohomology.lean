import OAI.AlgebraicGeometry.Comparison.Betti.Godement.TotalSections
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueHypercohomology

/-! # Hypercohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.Hypercohomology

noncomputable section

/-! The functorial Godement total computes the original derived hypercohomology of any nonnegative complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ)

local instance godementHypercohomologyExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves X) := HasExt.standard _
local instance godementHypercohomologyDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves X) :=
  HasDerivedCategory.standard _

def godementTotalComplexInt : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ :=
  (Bicomplex.godementTotal K).extend (ComplexShape.embeddingUpIntGE 0)

instance godementTotalComplexInt_nonnegative : (godementTotalComplexInt K).IsStrictlyGE 0 := by
  apply (CochainComplex.isStrictlyGE_iff _ 0).mpr
  intro n hn
  exact FlasqueNatQuasiIso.extend_zero_below (Bicomplex.godementTotal K) n hn

def godementTotalAugmentationInt :
    K.extend (ComplexShape.embeddingUpIntGE 0) ⟶ godementTotalComplexInt K :=
  HomologicalComplex.extendMap (Bicomplex.godementTotalAugmentation K) (ComplexShape.embeddingUpIntGE 0)

theorem godementTotalAugmentationInt_quasiIso : QuasiIso (godementTotalAugmentationInt K) :=
  (HomologicalComplex.quasiIso_extendMap_iff (Bicomplex.godementTotalAugmentation K)
    (ComplexShape.embeddingUpIntGE 0)).mpr (TotalQuasiIso.godementTotalAugmentation_quasiIso K)

def godementHypercohomologyEquiv (n : ℤ) :
    (FlasqueHypercohomology.integerGlobalSectionsComplex (godementTotalComplexInt K)).homology n ≃ₗ[ℂ]
      ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves X) 0).obj
        (ConstantSheafSections.standardConstantSheaf X) ⟶
          (DerivedCategory.Q.obj (K.extend (ComplexShape.embeddingUpIntGE 0)))⟦n⟧) := by
  let e := FlasqueHypercohomology.flasqueHypercohomologyEquiv (godementTotalComplexInt K) 0
    (FlasqueNatQuasiIso.extend_flasque (Bicomplex.godementTotal K) (TotalFlasque.godementTotal_isFlasque K)) n
  let r := DerivedCategory.Q.map (godementTotalAugmentationInt K)
  have hr : IsIso r := (DerivedCategory.isIso_Q_map_iff_quasiIso (ConstantSheafSections.ComplexSheaves X) _).mpr
    (godementTotalAugmentationInt_quasiIso K)
  let e' := (shiftFunctor (DerivedCategory (ConstantSheafSections.ComplexSheaves X)) n).mapIso (asIso r).symm
  exact e.trans (Linear.homCongr ℂ (Iso.refl _) e')

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.Hypercohomology
