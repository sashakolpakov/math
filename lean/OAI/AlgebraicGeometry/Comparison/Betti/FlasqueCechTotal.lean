import OAI.AlgebraicGeometry.Comparison.Betti.SectionResolutionTotal
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.FunctorAdditive
import OAI.AlgebraicGeometry.SheafCohomology.Cech.HorizontalComparison

/-! # Flasque Cech Total -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueCechTotal

noncomputable section

/-! The original global-section augmentation into the Čech total is a quasi-isomorphism for a nonnegative complex of flasque sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)

local instance cechGlobalSectionsAdditive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

def additiveSheafSectionCechBicomplex : HomologicalComplex₂ AddCommGrpCat.{0} (.up ℕ) (.up ℕ) :=
  ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K

def additiveGlobalComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K

def globalCechAugmentation (q : ℕ) : (additiveGlobalComplex K).X q ⟶
    ((FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).X q).X 0 :=
  SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation (K.X q) U

theorem globalCechAugmentation_comm (q q' : ℕ) :
    globalCechAugmentation U K q ≫ ((FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).d q q').f 0 =
      (additiveGlobalComplex K).d q q' ≫ globalCechAugmentation U K q' :=
  SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_naturality (U := U) (f := K.d q q')

theorem globalCechAugmentation_comp_d (q : ℕ) :
    globalCechAugmentation U K q ≫ ((FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).X q).d 0 1 = 0 :=
  SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d (K.X q) U

def globalCechTotalAugmentation : additiveGlobalComplex K ⟶
    (FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).total (.up ℕ) :=
  (SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (additiveSheafSectionCechBicomplex U K)) (additiveGlobalComplex K)
    (globalCechAugmentation U K) (fun q q' _ => globalCechAugmentation_comm U K q q')
    (globalCechAugmentation_comp_d U K)

theorem globalCechTotalAugmentation_quasiIso (hU : ⨆ i, U i = ⊤)
    (hK : ∀ p, TopCat.Sheaf.IsFlasque (K.X p)) : QuasiIso (globalCechTotalAugmentation U K) := by
  apply SectionResolutionTotal.additiveHorizontalEdge_quasiIso
  · intro q
    exact SheafCohomology.Cech.InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsNativeShortComplex_exact U (K.X q) hU
  · intro q
    exact SheafCohomology.Cech.InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsAugmentation_mono U (K.X q) hU
  · intro q p
    have := hK q
    exact SheafCohomology.Cech.FlasqueExact.TopCat.Sheaf.cechComplex_exactAt_succ_of_isFlasque (K.X q) U hU p

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueCechTotal
