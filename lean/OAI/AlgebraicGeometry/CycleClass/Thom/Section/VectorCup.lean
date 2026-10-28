import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupDegrees
import OAI.AlgebraicGeometry.CycleClass.Thom.HeadTailCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange

/-! # Vector Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorCup.Constructions

noncomputable section

/-! The actual regular-section vector class splits as the genuine
supported cup of its head and tail, in literal Fin.cons coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HeadTailCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) (r : Γ(Y.left, ⊤)) (s : Fin n → Γ(Y.left, ⊤))

theorem sectionVector_normalMapAt :
    Normal.CupDegrees.Constructions.normalMapAt (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y r) (VectorHeadChange.Constructions.sectionVectorEquation Y n s) (HeadTailCoordinates.Constructions.headTailCoordinates n) =
      VectorHeadChange.Constructions.sectionVectorEquation Y (n + 1) (Fin.cons r s) := by
  ext x : 1
  funext i
  cases i using Fin.cases <;> rfl

theorem sectionVector_mapsTo (A B : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (hr : Set.MapsTo (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y r) A ({0}ᶜ))
    (hs : Set.MapsTo (VectorHeadChange.Constructions.sectionVectorEquation Y n s) B ({0}ᶜ)) :
    Set.MapsTo (VectorHeadChange.Constructions.sectionVectorEquation Y (n + 1) (Fin.cons r s)) (A ∪ B) ({0}ᶜ) := by
  rw [← sectionVector_normalMapAt]
  exact Normal.CupDegrees.Constructions.normalMapAt_mapsTo _ _ _ hr hs

theorem sectionVectorCup_split (A B : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (hA : IsOpen A) (hB : IsOpen B)
    (hr : Set.MapsTo (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y r) A ({0}ᶜ))
    (hs : Set.MapsTo (VectorHeadChange.Constructions.sectionVectorEquation Y n s) B ({0}ᶜ)) :
    SupportedCupDegrees.Constructions.cupAt (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) A B hA hB 2 (2 * n) (2 * (n + 1)) (by omega)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y r) hr 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (VectorHeadChange.Constructions.sectionVectorEquation Y n s) hs (2 * n)
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n)) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (VectorHeadChange.Constructions.sectionVectorEquation Y (n + 1) (Fin.cons r s))
        (sectionVector_mapsTo Y n r s A B hr hs) (2 * (n + 1)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1)) :=
  (Normal.CupDegrees.Constructions.normalCupAt (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y r) (VectorHeadChange.Constructions.sectionVectorEquation Y n s) (HeadTailCoordinates.Constructions.headTailCoordinates n)
    hA hB (Nat.add_comm 1 n) hr hs).trans
      (ConcreteCategory.congr_hom (ThomOpenRestriction.Constructions.pairMap_congr (sectionVector_normalMapAt Y n r s) _
        (sectionVector_mapsTo Y n r s A B hr hs) (2 * (n + 1))) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1)))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorCup.Constructions
