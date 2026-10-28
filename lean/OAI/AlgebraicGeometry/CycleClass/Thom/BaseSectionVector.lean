import OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorCup
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange

/-! # Base Section Vector -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions

noncomputable section

/-! Actual section-vector equations on an ambient analytic open,
with head-and-tail cup splitting and elementary-change invariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions.Equation OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.HeadTailCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ElementaryEquationHomotopy.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

def baseSectionVector (n : ℕ) (s : Fin n → Γ(Y.left, ⊤)) : TopCat.of U ⟶ TopCat.of (Fin n → ℂ) :=
  IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU ≫ Section.VectorHeadChange.Constructions.sectionVectorEquation Y n s

def baseSectionScalar (s : Γ(Y.left, ⊤)) : TopCat.of U ⟶ TopCat.of ℂ :=
  IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU ≫ Section.VectorHeadChange.Constructions.sectionScalarEquation Y s

variable (n : ℕ) (r : Γ(Y.left, ⊤)) (s : Fin n → Γ(Y.left, ⊤))

theorem baseSectionVector_normalMapAt :
    Normal.CupDegrees.Constructions.normalMapAt (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r) (baseSectionVector j U hU n s) (HeadTailCoordinates.Constructions.headTailCoordinates n) =
      baseSectionVector j U hU (n + 1) (Fin.cons r s) := by
  ext x : 1
  funext i
  cases i using Fin.cases <;> rfl

theorem baseSectionVector_mapsTo (A B : Set U)
    (hr : Set.MapsTo (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r) A ({0}ᶜ))
    (hs : Set.MapsTo (baseSectionVector j U hU n s) B ({0}ᶜ)) :
    Set.MapsTo (baseSectionVector j U hU (n + 1) (Fin.cons r s)) (A ∪ B) ({0}ᶜ) := by
  rw [← baseSectionVector_normalMapAt]
  exact Normal.CupDegrees.Constructions.normalMapAt_mapsTo _ _ _ hr hs

theorem baseSectionVectorCup_split (A B : Set U) (hA : IsOpen A) (hB : IsOpen B)
    (hr : Set.MapsTo (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r) A ({0}ᶜ))
    (hs : Set.MapsTo (baseSectionVector j U hU n s) B ({0}ᶜ)) :
    SupportedCupDegrees.Constructions.cupAt (TopCat.of U) A B hA hB 2 (2 * n) (2 * (n + 1)) (by omega)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r) hr 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (baseSectionVector j U hU n s) hs (2 * n)
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (baseSectionVector j U hU (n + 1) (Fin.cons r s))
      (baseSectionVector_mapsTo j U hU n r s A B hr hs) (2 * (n + 1)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1)) :=
  (Normal.CupDegrees.Constructions.normalCupAt (BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU r) (baseSectionVector j U hU n s) (HeadTailCoordinates.Constructions.headTailCoordinates n)
    hA hB (Nat.add_comm 1 n) hr hs).trans
      (ConcreteCategory.congr_hom (ThomOpenRestriction.Constructions.pairMap_congr (baseSectionVector_normalMapAt j U hU n r s) _
        (baseSectionVector_mapsTo j U hU n r s A B hr hs) (2 * (n + 1))) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1)))

variable (a : Γ(Y.left, ⊤))

theorem baseSectionVector_adjusted :
    ElementaryEquationHomotopy.Constructions.adjustedEquation n (baseSectionVector j U hU (n + 1) (Fin.cons r s)) (baseSectionScalar j U hU a) =
      baseSectionVector j U hU (n + 1) (Fin.cons (r + a) s) := by
  ext x : 1
  exact congrArg (fun f => f (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x)) (Section.VectorHeadChange.Constructions.adjustedEquation_eq_sectionVector Y n r s a)

theorem baseSectionVector_zero_iff_head_change (ha : a ∈ Ideal.span (Set.range s)) (x : U) :
    baseSectionVector j U hU (n + 1) (Fin.cons (r + a) s) x = 0 ↔
      baseSectionVector j U hU (n + 1) (Fin.cons r s) x = 0 :=
  Section.VectorHeadChange.Constructions.sectionVector_zero_iff_head_change Y n r s a ha (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x)

theorem relativeCohomologyMap_base_head_change (ha : a ∈ Ideal.span (Set.range s)) (A : Set U)
    (hf : Set.MapsTo (baseSectionVector j U hU (n + 1) (Fin.cons r s)) A ({0}ᶜ))
    (hg : Set.MapsTo (baseSectionVector j U hU (n + 1) (Fin.cons (r + a) s)) A ({0}ᶜ)) (d : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (baseSectionVector j U hU (n + 1) (Fin.cons r s)) hf d =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (baseSectionVector j U hU (n + 1) (Fin.cons (r + a) s)) hg d := by
  let hzero := fun (y : U) hy => Section.VectorHeadChange.Constructions.tailIdeal_evaluation_zero Y n s a ha (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU y) hy
  exact (ElementaryEquationHomotopy.Constructions.relativeCohomologyMap_head_adjustment n (baseSectionVector j U hU (n + 1) (Fin.cons r s))
    (baseSectionScalar j U hU a) hzero A hf d).trans
      (ThomOpenRestriction.Constructions.pairMap_congr (baseSectionVector_adjusted j U hU n r s a) _ hg d)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions
