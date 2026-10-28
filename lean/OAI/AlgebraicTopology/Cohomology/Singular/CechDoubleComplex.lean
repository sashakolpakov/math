import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison
import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainComparison
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex
import OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation

/-! # Cech Double Complex -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CechDoubleComplex

noncomputable section

/-!
# The actual singular Čech double complex and its augmentations

The two indices are Čech degree followed by ordinary singular cochain degree.
The row augmentation is restriction of actual cover-small singular cochains;
its compatibility with the vertical differential follows from the genuine
singular pullback maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} (X : TopCat.{0})

/-- The local-to-small simplex map followed by the small inclusion is the
ordinary singular map of the subset inclusion. -/
theorem localSmallSingularMap_inclusion (V : ι → Set X) (i : ι) :
    SmallCochainCech.localSmallSingularMap X V i ≫ DeRham.Comparison.SmallSingularSet.smallSingularInclusion X V =
      TopCat.toSSet.map (show TopCat.of (V i) ⟶ X from
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.ext_apply
  intro σ
  apply (X.toSSetObjEquiv n).injective
  apply ContinuousMap.ext
  intro t
  rfl

/-- Restricting through the small simplices recovers ordinary restriction
to each member of the spatial family. -/
theorem smallSingularRestriction_local {R : Type} [Ring R]
    (V : ι → Set X) (M : ModuleCat.{0} R) (i : ι) :
    DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X V ≫ SmallCochainCech.smallSingularLocalRestriction X V M i =
      Functor.singularPullback M (show TopCat.of (V i) ⟶ X from
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) := by
  rw [DeRham.Comparison.SmallSingularCochains.smallSingularRestriction, SmallCochainCech.smallSingularLocalRestriction,
    ← Functor.simplicialPullback_comp, localSmallSingularMap_inclusion]
  rfl

variable (U : ι → Opens X) (M : ModuleCat.{0} ℂ)

/-- Actual restriction of cover-small cochains to a finite open intersection. -/
def smallSingularIntersectionRestriction {k : ℕ} (a : Fin (k + 1) → ι) :
    DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X)) ⟶
      Basic.singularCochains M (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) :=
  SmallCochainCech.smallSingularLocalRestriction X (fun i => (U i : Set X)) M (a 0) ≫
    Functor.singularPullback M ((Opens.toTopCat X).map
      (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)))

/-- The standard row augmentation is exactly this cochain restriction
to each singleton intersection. -/
@[simp]
theorem smallSingularIntersectionRestriction_f (n : ℕ) (a : Fin 1 → ι)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    (smallSingularIntersectionRestriction X U M a).f n c =
      SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M n c a := rfl

/-- The actual small-singular row augmentation commutes with the ordinary
singular coboundary in every internal degree. -/
theorem smallSingularCechStandardAugmentation_d (n : ℕ)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U ((DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).d n (n + 1)) 0
      (SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M n c) =
        SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M (n + 1)
          ((DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).d n (n + 1) c) := by
  funext a
  exact ConcreteCategory.congr_hom
    ((smallSingularIntersectionRestriction X U M a).comm n (n + 1)) c

/-- The two-step small restriction to an intersection equals the direct
ordinary singular restriction along its continuous inclusion. -/
theorem smallSingularRestriction_intersection {k : ℕ} (a : Fin (k + 1) → ι) :
    DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun i => (U i : Set X)) ≫
      smallSingularIntersectionRestriction X U M a =
        Functor.singularPullback M (show TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ X from
          TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) := by
  rw [smallSingularIntersectionRestriction, ← Category.assoc,
    smallSingularRestriction_local, ← Functor.singularPullback_comp]
  rfl

/-- The genuine Čech double complex of the actual singular cochain presheaf.
The first degree is Čech degree and the second is singular cochain degree. -/
abbrev singularCechDoubleComplex :
    HomologicalComplex₂ (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex U (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)

/-- Bidegree `(k,n)` consists of singular degree-`n` cochains on the actual
finite open intersections indexed by Čech `k`-tuples. -/
@[simp]
theorem singularCechDoubleComplex_XX (k n : ℕ) :
    ((singularCechDoubleComplex X U M).X k).X n =
      ModuleCat.of ℂ (DeRham.Comparison.SmoothCech.CechCochain (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U k) := rfl

/-- The horizontal differential is the signed sum of actual restrictions. -/
@[simp]
theorem singularCechDoubleComplex_d_f (k n : ℕ) :
    ((singularCechDoubleComplex X U M).d k (k + 1)).f n =
      ModuleCat.ofHom (DeRham.Comparison.SmoothCech.cechDelta (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U k) :=
  DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex_d_f U (DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) k n

/-- The vertical differential is the actual singular coboundary on each
intersection, with the totalization sign supplied by the native total complex. -/
@[simp]
theorem singularCechDoubleComplex_X_d (k n : ℕ) :
    ((singularCechDoubleComplex X U M).X k).d n (n + 1) =
      ModuleCat.ofHom
        (DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U ((DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).d n (n + 1)) k) := rfl

/-- The horizontal rows are exactly the previously checked singular Čech rows. -/
@[simp]
theorem singularCechDoubleComplex_row (n : ℕ) :
    (singularCechDoubleComplex X U M).flip.X n =
      DeRham.Comparison.SmoothCech.cechComplex (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U := rfl

/-- Every positive horizontal degree is exact, for any open family: the
augmentation resolves cochains on simplices small for that family. -/
theorem singularCechDoubleComplex_row_exact (k n : ℕ) :
    ((singularCechDoubleComplex X U M).flip.X n).ExactAt (k + 1) :=
  SmallCochainCechComparison.singularCochainCech_exactAt_succ X U M n k

/-- The actual small-cochain restrictions assemble into a cochain map to
column zero because they commute with the singular coboundary. -/
def smallSingularCechColumnAugmentation :
    DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X)) ⟶
      (singularCechDoubleComplex X U M).X 0 where
  f n := ModuleCat.ofHom (SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [singularCechDoubleComplex_X_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact smallSingularCechStandardAugmentation_d X U M i c

@[simp]
theorem smallSingularCechColumnAugmentation_f (n : ℕ) :
    (smallSingularCechColumnAugmentation X U M).f n =
      ModuleCat.ofHom (SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M n) := rfl

/-- The first horizontal differential kills the actual small augmentation. -/
theorem smallSingularCechColumnAugmentation_horizontal :
    smallSingularCechColumnAugmentation X U M ≫
      (singularCechDoubleComplex X U M).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    smallSingularCechColumnAugmentation_f, singularCechDoubleComplex_d_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact SmallCochainCechComparison.smallSingularCechStandardAugmentation_delta X U M n c

/-- Global singular cochains augment column zero by their actual restriction
through the small singular simplices. -/
def globalSingularCechColumnAugmentation :
    Basic.singularCochains M X ⟶ (singularCechDoubleComplex X U M).X 0 :=
  DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun i => (U i : Set X)) ≫
    smallSingularCechColumnAugmentation X U M

/-- The global augmentation really is restriction along each intersection's
continuous inclusion into the original space. -/
theorem globalSingularCechColumnAugmentation_apply (n : ℕ)
    (c : (Basic.singularCochains M X).X n) (a : Fin 1 → ι) :
    ((globalSingularCechColumnAugmentation X U M).f n c) a =
      (Functor.singularPullback M (show TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ X from
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).f n c := by
  have h := congrArg (fun f : Basic.singularCochains M X ⟶
      Basic.singularCochains M (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) => f.f n)
    (smallSingularRestriction_intersection X U M a)
  exact ConcreteCategory.congr_hom h c

/-- Global restrictions agree on pairwise intersections. -/
theorem globalSingularCechColumnAugmentation_horizontal :
    globalSingularCechColumnAugmentation X U M ≫
      (singularCechDoubleComplex X U M).d 0 1 = 0 := by
  rw [globalSingularCechColumnAugmentation, Category.assoc,
    smallSingularCechColumnAugmentation_horizontal, comp_zero]

/-- The native total complex of the genuine singular Čech double complex. -/
abbrev singularCechTotal : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  (singularCechDoubleComplex X U M).total (ComplexShape.up ℕ)

/-- The small-cochain augmentation into the actual native total complex. -/
def smallSingularCechAugmentation :
    DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X)) ⟶ singularCechTotal X U M :=
  DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (singularCechDoubleComplex X U M)
    (smallSingularCechColumnAugmentation X U M)
    (smallSingularCechColumnAugmentation_horizontal X U M)

/-- The global singular augmentation into the same native total complex. -/
def globalSingularCechAugmentation : Basic.singularCochains M X ⟶ singularCechTotal X U M :=
  DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (singularCechDoubleComplex X U M)
    (globalSingularCechColumnAugmentation X U M)
    (globalSingularCechColumnAugmentation_horizontal X U M)

/-- The total small augmentation is supported in the actual zeroth Čech column. -/
@[simp]
theorem smallSingularCechAugmentation_f (n : ℕ) :
    (smallSingularCechAugmentation X U M).f n =
      (smallSingularCechColumnAugmentation X U M).f n ≫
        (singularCechDoubleComplex X U M).ιTotal (ComplexShape.up ℕ) 0 n n (by simp) := rfl

/-- The total global augmentation is supported in the same actual column. -/
@[simp]
theorem globalSingularCechAugmentation_f (n : ℕ) :
    (globalSingularCechAugmentation X U M).f n =
      (globalSingularCechColumnAugmentation X U M).f n ≫
        (singularCechDoubleComplex X U M).ιTotal (ComplexShape.up ℕ) 0 n n (by simp) := rfl

/-- The canonical global-to-small restriction intertwines the two actual
augmentations, as an equality of cochain maps. -/
theorem globalSingularCechAugmentation_eq :
    globalSingularCechAugmentation X U M =
      DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun i => (U i : Set X)) ≫
        smallSingularCechAugmentation X U M := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, smallSingularCechAugmentation_f,
    globalSingularCechAugmentation_f]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicTopology.Cohomology.Singular.CechDoubleComplex
