import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueSectionCokernels
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctor

/-! # Thom Shift Sections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomShiftSections.Constructions

noncomputable section

/-! The actual shifted Thom sheaf resolution computes the original relative cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem cochainDegreeShift_boundary_eq_zero (k n : ℕ)
    (hn : (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).BoundaryGE n) : n=0 := by
  cases n with
  | zero => rfl
  | succ n => exact False.elim ((RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k).not_boundaryGE_next
      (show (ComplexShape.up ℕ).Rel n (n+1) from rfl) hn)

variable {X : TopCat.{0}}

def rationalFlasqueGoodShiftSectionsIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (k : ℕ)
    (he : ∀ n, n<k → K.ExactAt n) (U : Opens X) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K).truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k) ≅
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) :=
  GoodShiftFunctor.Constructions.goodShiftFunctorIso (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U) K k (by
    intro n hn
    have hn0 := cochainDegreeShift_boundary_eq_zero k n hn
    subst n
    exact FlasqueSectionCokernels.Constructions.rationalFlasqueSections_preservesRightHomologyOf K hK k he U k le_rfl)

def rationalFlasqueGoodShiftSectionCohomologyIso
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (k : ℕ)
    (he : ∀ n, n<k → K.ExactAt n) (U : Opens X) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))).homology n ≅
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K).homology (k+n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n).mapIso
      (rationalFlasqueGoodShiftSectionsIso K hK k he U).symm ≪≫
    GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U K) k n

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

def regularThomGoodShiftSectionCohomologyIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)).homology n ≅
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSections (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        Z.regularThomComplementOpen U).homology (2*p+n) :=
  rationalFlasqueGoodShiftSectionCohomologyIso Z.regularThomSheafComplex
    (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen)
    (2*p) (fun i hi => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z i (by omega)) U n

/-- Every open set retains its actual relative singular cohomology after the shift. -/
def regularThomGoodShiftSectionsRelativeIso (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)).homology n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) (2*p+n) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ
    (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen U
  exact regularThomGoodShiftSectionCohomologyIso Z U n ≪≫
    (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen U) (2*p+n)).symm

/-- Global sections compute the original support cohomology in every shifted degree. -/
def regularThomGoodShiftGlobalRelativeIso (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex (⊤ : Opens Z.regularAmbientSpace)
      (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)).homology n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ (2*p+n) :=
  regularThomGoodShiftSectionCohomologyIso Z ⊤ n ≪≫
    (CycleClass.Geometric.GlobalSupportPurity.Cycles.relativeSupportedGlobalCohomologyIso (TopCat.of Z.regularAmbientSpace)
      Z.regularThomComplementOpen (2*p+n)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomShiftSections.Constructions
