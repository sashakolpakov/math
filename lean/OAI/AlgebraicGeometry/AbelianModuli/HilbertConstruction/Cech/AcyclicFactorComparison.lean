import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FirstCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalSectionsComplex

/-! # Acyclic Factor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicFactorComparison.IntrinsicCech

noncomputable section

/-! Acyclic restriction-pushforward factors make the actual sheaf Cech
resolution an acyclic resolution. Its top sections compute genuine
cohomology in every degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u})
variable {ι : Type u} (U : ι → Opens X)

def cechTopSectionsComplexIso :
    AcyclicResolutionCohomology.IntrinsicCech.sheafTopSectionsComplex (IntrinsicCech.SheafComplex.cechComplex F U) ≅ (cechComplexFunctor U).obj F.obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U n).toAddCommGrpIso) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      change (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom ≫
          ((cechComplexFunctor U).obj F.obj).d i (i + 1) =
        ((IntrinsicCech.SheafComplex.cechComplex F U).d i (i + 1)).hom.app (op ⊤) ≫
          (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom
      rw [IntrinsicCech.SheafComplex.cechComplex_d F U i]
      exact TopSectionDifferential.IntrinsicCech.cechTopSectionsAddEquiv_d F U i)

variable [Finite ι]

def cechCohomologyIsoOfAcyclicFactors (hU : iSup U = ⊤)
    (hF : ∀ p q (i : Fin (p + 1) → ι),
      Subsingleton (CategoryTheory.Sheaf.H (IntrinsicCech.SheafTerms.cechTermFactor F U p i) (q + 1))) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology n ≅
      AddCommGrpCat.of (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n :
        _ ⥤ AddCommGrpCat.{u}).obj F)) := by
  let K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ := IntrinsicCech.SheafComplex.cechComplex F U
  let e : F ⟶ K.X 0 := SheafAugmentation.IntrinsicCech.cechAugmentation F U
  have : Mono e := SheafResolution.IntrinsicCech.cechAugmentation_mono F U hU
  have w : e ≫ K.d 0 1 = 0 := by
    rw [IntrinsicCech.SheafComplex.cechComplex_d F U 0]
    exact SheafAugmentation.IntrinsicCech.cechAugmentation_comp F U
  have haug : (ShortComplex.mk e (K.d 0 1) w).Exact := by
    change (SheafAugmentation.IntrinsicCech.cechAugmentedShortComplex F U).Exact
    exact ZeroCycleStalks.IntrinsicCech.cechAugmentedShortComplex_exact F U hU
  have hpos (p : ℕ) : (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K p).Exact := by
    simpa only [K, AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex, IntrinsicCech.SheafComplex.cechComplex_d, IntrinsicCech.SheafComplex.cechComplex_X,
      Nat.add_assoc] using PositiveCycleStalks.IntrinsicCech.cechShortComplex_exact F U hU p
  have hK (p q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)) :=
    FirstCohomology.IntrinsicCech.sheafCohomology_finiteProduct_vanish (IntrinsicCech.SheafTerms.cechTermFactor F U p) (q + 1) (hF p q)
  exact (HomologicalComplex.homologyMapIso (cechTopSectionsComplexIso F U) n).symm ≪≫
    AcyclicResolutionCohomology.IntrinsicCech.acyclicResolutionCohomologyIso K e w haug hpos hK n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicFactorComparison.IntrinsicCech
