import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVectorChange
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport

/-! # Base Vector Normal -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport

/-! The literal zero support of an actual section vector on an
ambient open, with its exact head-and-tail decomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

def vectorZeroImage (n : ℕ) (s : Fin n → Γ(Y.left, ⊤)) :
    {x : U // BaseSectionVector.Constructions.baseSectionVector j U hU n s x = 0} → U := Subtype.val

theorem vectorZeroImage_range (n : ℕ) (s : Fin n → Γ(Y.left, ⊤)) :
    Set.range (vectorZeroImage j U hU n s) = {x : U | BaseSectionVector.Constructions.baseSectionVector j U hU n s x = 0} :=
  Subtype.range_coe

theorem vectorZeroImage_openComplement (n : ℕ) (s : Fin n → Γ(Y.left, ⊤)) :
    IsOpen (Set.range (vectorZeroImage j U hU n s))ᶜ := by
  rw [vectorZeroImage_range]
  exact (isClosed_eq (BaseSectionVector.Constructions.baseSectionVector j U hU n s).hom.continuous continuous_const).isOpen_compl

theorem vectorZeroImage_mapsTo (n : ℕ) (s : Fin n → Γ(Y.left, ⊤)) :
    Set.MapsTo (BaseSectionVector.Constructions.baseSectionVector j U hU n s) (Set.range (vectorZeroImage j U hU n s))ᶜ ({0}ᶜ) :=
  fun x hx hz => hx ⟨⟨x, hz⟩, rfl⟩

theorem vectorZeroImage_cons (n : ℕ) (r : Γ(Y.left, ⊤)) (s : Fin n → Γ(Y.left, ⊤)) :
    Set.range (vectorZeroImage j U hU (n + 1) (Fin.cons r s)) =
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y r)) ∩
        Set.range (vectorZeroImage j U hU n s) := by
  rw [vectorZeroImage_range, vectorZeroImage_range, ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range, GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
  ext x
  change BaseSectionVector.Constructions.baseSectionVector j U hU (n + 1) (Fin.cons r s) x = 0 ↔
    DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x) r = 0 ∧
      BaseSectionVector.Constructions.baseSectionVector j U hU n s x = 0
  constructor
  · intro h
    exact ⟨congrFun h 0, funext (fun i => congrFun h i.succ)⟩
  · rintro ⟨hr, hs⟩
    funext i
    cases i using Fin.cases with
    | zero => exact hr
    | succ i => exact congrFun hs i

theorem vectorZeroImage_head_change (n : ℕ) (r : Γ(Y.left, ⊤)) (s : Fin n → Γ(Y.left, ⊤))
    (a : Γ(Y.left, ⊤)) (ha : a ∈ Ideal.span (Set.range s)) :
    Set.range (vectorZeroImage j U hU (n + 1) (Fin.cons (r + a) s)) =
      Set.range (vectorZeroImage j U hU (n + 1) (Fin.cons r s)) := by
  rw [vectorZeroImage_range, vectorZeroImage_range]
  ext x
  exact BaseSectionVector.Constructions.baseSectionVector_zero_iff_head_change j U hU n r s a ha x

end AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport

namespace AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class

/-! The actual supported normal class of a section vector, with its
precise transport under a constructed elementary head change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionChange.Constructions.Equation
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

def vectorNormalClass (n : ℕ) (s : Fin n → Γ(Y.left, ⊤)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (Set.range (SectionSupport.vectorZeroImage j U hU n s))ᶜ (2 * n) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector j U hU n s)
    (SectionSupport.vectorZeroImage_mapsTo j U hU n s) (2 * n) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n)

theorem baseSectionVector_one (s : Fin 1 → Γ(Y.left, ⊤)) :
    BaseSectionVector.Constructions.baseSectionVector j U hU 1 s = BaseSectionChange.Constructions.Equation.baseSectionEquation j U hU (s 0) := by
  ext x : 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem vectorZeroImage_one (s : Fin 1 → Γ(Y.left, ⊤)) :
    Set.range (SectionSupport.vectorZeroImage j U hU 1 s) =
      Set.range (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y (s 0))) := by
  rw [SectionSupport.vectorZeroImage_range, ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range, GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
  ext x
  constructor
  · intro hx
    exact congrFun hx 0
  · intro hx
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hx

variable (n : ℕ) (r : Γ(Y.left, ⊤)) (s : Fin n → Γ(Y.left, ⊤)) (a : Γ(Y.left, ⊤))
  (ha : a ∈ Ideal.span (Set.range s))

include ha in
theorem headChange_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    (Set.range (SectionSupport.vectorZeroImage j U hU (n + 1) (Fin.cons (r + a) s)))ᶜ
    (Set.range (SectionSupport.vectorZeroImage j U hU (n + 1) (Fin.cons r s)))ᶜ :=
  fun _ hx hy => hx ((SectionSupport.vectorZeroImage_head_change j U hU n r s a ha).symm ▸ hy)

theorem vectorNormalClass_head_change :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (headChange_mapsTo j U hU n r s a ha) (2 * (n + 1))
      (vectorNormalClass j U hU (n + 1) (Fin.cons r s)) =
    vectorNormalClass j U hU (n + 1) (Fin.cons (r + a) s) := by
  let hf := (SectionSupport.vectorZeroImage_mapsTo j U hU (n + 1) (Fin.cons r s)).comp
    (headChange_mapsTo j U hU n r s a ha)
  have hcomp := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (BaseSectionVector.Constructions.baseSectionVector j U hU (n + 1) (Fin.cons r s)) (headChange_mapsTo j U hU n r s a ha)
    (SectionSupport.vectorZeroImage_mapsTo j U hU (n + 1) (Fin.cons r s)) (2 * (n + 1))
  exact (ConcreteCategory.congr_hom hcomp (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1))).trans
    (ConcreteCategory.congr_hom (BaseSectionVector.Constructions.relativeCohomologyMap_base_head_change j U hU n r s a ha
      (Set.range (SectionSupport.vectorZeroImage j U hU (n + 1) (Fin.cons (r + a) s)))ᶜ hf
      (SectionSupport.vectorZeroImage_mapsTo j U hU (n + 1) (Fin.cons (r + a) s)) (2 * (n + 1)))
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (n + 1)))

end AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class

namespace AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Change

/-! The actual section-vector zero support and normal class are
preserved by restricting the algebraic base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVectorChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y Z N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom] [IsIntegral N.left] [Smooth N.hom]
  (j : Y ⟶ N) (j' : Z ⟶ N) [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  (k : Z ⟶ Y) (hk : k ≫ j = j') (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hU' : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j'))
  (n : ℕ) (s : Fin n → Γ(Y.left, ⊤))

include hk

theorem vectorZeroImage_change :
    Set.range (SectionSupport.vectorZeroImage j' U hU' n (fun i => k.left.appTop (s i))) =
      Set.range (SectionSupport.vectorZeroImage j U hU n s) := by
  rw [SectionSupport.vectorZeroImage_range, SectionSupport.vectorZeroImage_range]
  exact congrArg (fun f : TopCat.of U ⟶ TopCat.of (Fin n → ℂ) => {x : U | f x = 0})
    (BaseSectionVectorChange.Constructions.baseSectionVector_change j j' k hk U hU hU' n s)

theorem vectorChange_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    (Set.range (SectionSupport.vectorZeroImage j' U hU' n (fun i => k.left.appTop (s i))))ᶜ
    (Set.range (SectionSupport.vectorZeroImage j U hU n s))ᶜ :=
  fun _ hx hy => hx ((vectorZeroImage_change j j' k hk U hU hU' n s).symm ▸ hy)

theorem vectorNormalClass_change :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (vectorChange_mapsTo j j' k hk U hU hU' n s) (2 * n) (Class.vectorNormalClass j U hU n s) =
    Class.vectorNormalClass j' U hU' n (fun i => k.left.appTop (s i)) := by
  let hf := (SectionSupport.vectorZeroImage_mapsTo j U hU n s).comp (vectorChange_mapsTo j j' k hk U hU hU' n s)
  have hcomp := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (BaseSectionVector.Constructions.baseSectionVector j U hU n s) (vectorChange_mapsTo j j' k hk U hU hU' n s)
    (SectionSupport.vectorZeroImage_mapsTo j U hU n s) (2 * n)
  exact (ConcreteCategory.congr_hom hcomp (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n)).trans
    (ConcreteCategory.congr_hom (ThomOpenRestriction.Constructions.pairMap_congr (BaseSectionVectorChange.Constructions.baseSectionVector_change j j' k hk U hU hU' n s).symm hf
      (SectionSupport.vectorZeroImage_mapsTo j' U hU' n (fun i => k.left.appTop (s i))) (2 * n)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n))

end AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Change

end

end OAI
