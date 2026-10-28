import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism

/-! # Cover Refinement Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementQuasiIso

noncomputable section

/-! Refinement between acyclic open covers is a quasi-isomorphism on
the original full Čech complexes, including degree zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism

universe u
variable {X : TopCat.{u}} {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

theorem degree_zero : AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZero.cechGlobalSectionsToHZero U F ≫
    HomologicalComplex.homologyMap (CoverRefinement.map U V r F.obj) 0 = AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZero.cechGlobalSectionsToHZero V F := by
  let K := (cechComplexFunctor U).obj F.obj
  let L := (cechComplexFunctor V).obj F.obj
  let φ := CoverRefinement.map U V r F.obj
  have h : K.liftCycles (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U) 1 (by simp)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationComplex.IntrinsicCech.cechGlobalSectionsAugmentation_comp_d F U) ≫ HomologicalComplex.cyclesMap φ 0 =
      L.liftCycles (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F V) 1 (by simp)
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationComplex.IntrinsicCech.cechGlobalSectionsAugmentation_comp_d F V) := by
    apply (cancel_mono (L.iCycles 0)).mp
    dsimp only [K, L, φ]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
    exact CoverRefinement.augmentation U V r F
  change (K.liftCycles _ 1 _ _ ≫ K.homologyπ 0) ≫ HomologicalComplex.homologyMap φ 0 =
    L.liftCycles _ 1 _ _ ≫ L.homologyπ 0
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, h]

theorem top_degree_zero : AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.TopDegreeZero.cechTopSectionsToHZero U F ≫
    HomologicalComplex.homologyMap (CoverRefinement.map U V r F.obj) 0 = AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.TopDegreeZero.cechTopSectionsToHZero V F := by
  unfold AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.TopDegreeZero.cechTopSectionsToHZero
  rw [Category.assoc, degree_zero]

theorem quasiIso (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (haU : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (haV : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic V F) :
    QuasiIso (CoverRefinement.map U V r F.obj) := by
  rw [_root_.quasiIso_iff]
  intro n
  cases n with
  | zero =>
    have h := top_degree_zero U V r F
    change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso U F hU).hom ≫
      HomologicalComplex.homologyMap (CoverRefinement.map U V r F.obj) 0 =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso V F hV).hom at h
    have he : HomologicalComplex.homologyMap (CoverRefinement.map U V r F.obj) 0 =
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso U F hU).inv ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso V F hV).hom := by
      apply (cancel_epi (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZeroIsomorphism.cechTopSectionsHZeroIso U F hU).hom).mp
      simpa only [Iso.hom_inv_id_assoc] using h
    rw [quasiIsoAt_iff_isIso_homologyMap, he]
    infer_instance
  | succ n =>
    have h := CoverRefinementCohomology.rightDerived U V r F hU hV haU haV n
    have he : HomologicalComplex.homologyMap (CoverRefinement.map U V r F.obj) (n + 1) =
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso U F hU haU n).hom ≫
          (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso V F hV haV n).inv := by
      apply (cancel_mono (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso V F hV haV n).hom).mp
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
    rw [quasiIsoAt_iff_isIso_homologyMap, he]
    infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementQuasiIso
