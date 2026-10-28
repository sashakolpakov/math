import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalChartPurity
import OAI.AlgebraicTopology.Cohomology.Singular.SupportedStalk

/-! # Normal Support Germ -/

namespace OAI.AlgebraicGeometry

noncomputable section

section

/-!
# Purity of actual supported singular-sheaf stalks

The supported complex is the genuine kernel of sheaf restriction to the
open complement. Its verified relative-cohomology comparison, followed by
the cofinal normal-neighborhood computation, gives purity at an embedded
point. The normalized top class belongs to the actual supported stalk.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf OAI.AlgebraicTopology.Cohomology.Singular.SupportedStalk

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {M N E F : Type} [TopologicalSpace N] [MetrizableSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

/-- The actual supported-stalk comparison with the relative-cohomology
stalk, after identifying the given open set with the image complement. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkRelativeRangeIso (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O) (f x)).homology n ≅
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N)
        (Set.range f)ᶜ n).stalk (f x) :=
  AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedStalkRelativeCohomologyIso ℚ (TopCat.of N) O (f x) n ≪≫
    eqToIso (congrArg (fun A : Set N =>
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of N) A n).stalk (f x)) hO)

/-- The actual supported singular-sheaf stalk has the cohomology of the
punctured normal vector space, via genuine germs and normal coordinates. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkNormalCohomologyIso (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O) (f x)).homology n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n :=
  ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkRelativeRangeIso (f := f) (x := x) O hO n ≪≫
    (P.normalStalkCohomologyIso n).symm

variable [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- Top supported-stalk cohomology is the one-dimensional rational module,
with its normalization transported by the actual complex normal model. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkTopCohomologyIso (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) :
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O)
        (f x)).homology (2 * Module.finrank ℂ F) ≅ ModuleCat.of ℚ ℚ :=
  P.supportedStalkNormalCohomologyIso O hO (2 * Module.finrank ℂ F) ≪≫
    CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso F

/-- The normalized rational class in the actual supported stalk. -/
def ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedRationalStalkClass (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) :
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O)
        (f x)).homology (2 * Module.finrank ℂ F) :=
  (P.supportedStalkTopCohomologyIso O hO).inv 1

@[simp]
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedRationalStalkClass_normalization (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) :
    (P.supportedStalkTopCohomologyIso O hO).hom (P.supportedRationalStalkClass O hO) = 1 :=
  (P.supportedStalkTopCohomologyIso O hO).toLinearEquiv.apply_symm_apply 1

theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedRationalStalkClass_ne_zero (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) : P.supportedRationalStalkClass O hO ≠ 0 := by
  intro h
  have hn := P.supportedRationalStalkClass_normalization O hO
  rw [h, map_zero] at hn
  exact zero_ne_one hn

include P in
/-- The actual supported stalk is zero outside the top normal degree. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalk_homology_isZero (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) (n : ℕ) (hn : n ≠ 2 * Module.finrank ℂ F) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O)
        (f x)).homology n) :=
  (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology_isZero F n hn).of_iso
    (P.supportedStalkNormalCohomologyIso O hO n)

include P in
/-- In particular the actual supported stalk vanishes below real codimension. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalk_homology_isZero_of_lt (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) (n : ℕ) (hn : n < 2 * Module.finrank ℂ F) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O)
        (f x)).homology n) :=
  P.supportedStalk_homology_isZero O hO n (Nat.ne_of_lt hn)

include P in
/-- Purity also expresses genuine exactness of the supported stalk complex. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalk_exactAt (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) (n : ℕ) (hn : n ≠ 2 * Module.finrank ℂ F) :
    (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O) (f x)).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact P.supportedStalk_homology_isZero O hO n hn

include P in
/-- The top normal degree is the only nonzero supported-stalk degree. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalk_homology_isZero_iff (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ) (n : ℕ) :
    IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O)
        (f x)).homology n) ↔ n ≠ 2 * Module.finrank ℂ F := by
  refine ⟨?_, P.supportedStalk_homology_isZero O hO n⟩
  intro hz hn
  subst n
  let : Subsingleton ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O)
        (f x)).homology (2 * Module.finrank ℂ F)) := ModuleCat.subsingleton_of_isZero hz
  exact P.supportedRationalStalkClass_ne_zero O hO (Subsingleton.elim _ _)

/-- Normalization one uniquely characterizes the actual top supported class. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedRationalStalkClass_unique (O : Opens (TopCat.of N))
    (hO : (O : Set N) = (Set.range f)ᶜ)
    (a : (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) (TopCat.of N) O)
        (f x)).homology (2 * Module.finrank ℂ F))
    (ha : (P.supportedStalkTopCohomologyIso O hO).hom a = 1) :
    a = P.supportedRationalStalkClass O hO := by
  apply (P.supportedStalkTopCohomologyIso O hO).toLinearEquiv.injective
  exact ha.trans (P.supportedRationalStalkClass_normalization O hO).symm

/-- Shrinking a genuine normal neighborhood in the same chart leaves the
actual supported-stalk class unchanged. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedRationalStalkClass_restrict (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
    (hQP : Q.neighborhood ⊆ P.neighborhood) (hchart : Q.ambientChart = P.ambientChart)
    (O : Opens (TopCat.of N)) (hO : (O : Set N) = (Set.range f)ᶜ) :
    P.supportedRationalStalkClass O hO = Q.supportedRationalStalkClass O hO := by
  have he : P.normalStalkCohomologyIso (2 * Module.finrank ℂ F) =
      Q.normalStalkCohomologyIso (2 * Module.finrank ℂ F) :=
    Iso.ext (P.normalStalkCohomologyIso_hom_eq Q hQP hchart (2 * Module.finrank ℂ F))
  unfold ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedRationalStalkClass ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkTopCohomologyIso
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkNormalCohomologyIso
  rw [he]

end

/-!
# The normalized local normal class in the actual supported stalk

The cohomology map of the genuine relative-to-supported cochain germ sends
the independently constructed rational normal class to the normalized
class in the actual supported stalk. The open complement is the literal
complement of the closed image, so the comparison introduces no transport
of the removed subset.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SupportedStalk

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {M N E F : Type} [TopologicalSpace N] [MetrizableSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (hclosed : IsClosed (Set.range f))

/-- The actual relative-to-supported cochain germ becomes precisely the
previously defined relative-cohomology germ under the supported-stalk comparison. -/
@[reassoc]
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.relativeToSupportedStalkCohomology_range (n : ℕ) :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm (ModuleCat.of ℚ ℚ) (TopCat.of N)
          ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ P.openNeighborhood
          (f x) P.point_mem_neighborhood) n ≫
        (ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkRelativeRangeIso (f := f) (x := x)
          ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ rfl n).hom =
      P.relativeCohomologyGerm n := by
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkRelativeRangeIso, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedStalkRelativeCohomologyIso_germ ℚ (TopCat.of N)
    ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ P.openNeighborhood
    (f x) P.point_mem_neighborhood n

variable [NormedSpace ℝ E]

/-- Pullback in genuine normal coordinates, followed by the actual
supported germ and the normal-model comparison, is the identity. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap_supportedStalkNormal (n : ℕ) :
    P.normalCohomologyMap (ModuleCat.of ℚ ℚ) n ≫
        HomologicalComplex.homologyMap
          (AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm (ModuleCat.of ℚ ℚ) (TopCat.of N)
            ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ P.openNeighborhood
            (f x) P.point_mem_neighborhood) n ≫
        (P.supportedStalkNormalCohomologyIso
          ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ rfl n).hom =
      𝟙 (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of F) ({0}ᶜ : Set F) n) := by
  dsimp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.supportedStalkNormalCohomologyIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc _ _ (P.normalStalkCohomologyIso n).inv,
    P.relativeToSupportedStalkCohomology_range hclosed n,
    ← Category.assoc, ← P.normalStalkCohomologyIso_hom n, Iso.hom_inv_id]

variable [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- The actual cohomology map of the relative-to-supported germ preserves
the independently defined rational normal-class normalization. -/
theorem ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.rationalClass_toSupportedStalk :
    HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm (ModuleCat.of ℚ ℚ) (TopCat.of N)
          ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ P.openNeighborhood
          (f x) P.point_mem_neighborhood) (2 * Module.finrank ℂ F) P.rationalClass =
      P.supportedRationalStalkClass ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ rfl := by
  apply P.supportedRationalStalkClass_unique ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ rfl
  rw [P.rationalClass_eq_pullback]
  change (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso F).hom
    ((P.supportedStalkNormalCohomologyIso
      ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ rfl (2 * Module.finrank ℂ F)).hom
      (HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm (ModuleCat.of ℚ ℚ) (TopCat.of N)
          ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ P.openNeighborhood
          (f x) P.point_mem_neighborhood) (2 * Module.finrank ℂ F)
        (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F)
          (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F)))) = 1
  have h : (P.supportedStalkNormalCohomologyIso
      ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ rfl (2 * Module.finrank ℂ F)).hom
      (HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm (ModuleCat.of ℚ ℚ) (TopCat.of N)
          ⟨(Set.range f)ᶜ, hclosed.isOpen_compl⟩ P.openNeighborhood
          (f x) P.point_mem_neighborhood) (2 * Module.finrank ℂ F)
        (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * Module.finrank ℂ F)
          (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F))) = CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F :=
    ConcreteCategory.congr_hom
      (P.normalCohomologyMap_supportedStalkNormal hclosed (2 * Module.finrank ℂ F))
      (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F)
  exact (congrArg (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso F).hom h).trans
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass_normalization F)

end

end OAI.AlgebraicGeometry
