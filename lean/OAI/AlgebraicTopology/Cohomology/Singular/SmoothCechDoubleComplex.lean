import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallCech
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSections
import OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation

/-! # Smooth Cech Double Complex -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex

noncomputable section

/-!
# The actual manifold-smooth singular Čech double complex

The horizontal degree is Čech degree and the vertical degree is the genuine
smooth singular cochain degree. Restriction of actual small smooth cochains
gives the row augmentation. Its compatibility with the smooth coboundary
produces the native total augmentation, and the global augmentation agrees
with the generic presheaf-section augmentation under the canonical top-open
identification.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor
open scoped Simplicial _root_.Manifold ContDiff

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Opens X) (A : ModuleCat.{0} ℂ)

/-- Actual restriction of cover-small smooth cochains to a finite open
intersection, through one of its containing cover members. -/
def smallManifoldSmoothIntersectionRestriction {k : ℕ} (a : Fin (k + 1) → ι) :
    ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X)) ⟶
      ManifoldSmooth.manifoldSmoothCochains E A (DeRham.Comparison.SmoothCech.cechIntersection U a) :=
  ManifoldSmoothSmall.manifoldSmoothSmallLocalRestriction E A X U (a 0) ≫
    ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E X A (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le U a 0))

/-- The existing standard row augmentation is the same actual restriction. -/
@[simp]
theorem smallManifoldSmoothIntersectionRestriction_f (n : ℕ) (a : Fin 1 → ι)
    (c : (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n) :
    (smallManifoldSmoothIntersectionRestriction E X U A a).f n c =
      ManifoldSmoothSmallCech.manifoldSmoothSmallCechStandardAugmentation E X U A n c a := rfl

/-- The actual small-smooth row augmentation commutes with the smooth
singular coboundary on every intersection. -/
theorem manifoldSmoothSmallCechStandardAugmentation_d (n : ℕ)
    (c : (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n) :
    DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U ((ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A).d n (n + 1)) 0
      (ManifoldSmoothSmallCech.manifoldSmoothSmallCechStandardAugmentation E X U A n c) =
        ManifoldSmoothSmallCech.manifoldSmoothSmallCechStandardAugmentation E X U A (n + 1)
          ((ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).d n (n + 1) c) := by
  funext a
  exact ConcreteCategory.congr_hom
    ((smallManifoldSmoothIntersectionRestriction E X U A a).comm n (n + 1)) c

/-- Global-to-small restriction followed by intersection restriction is
the smooth pullback along the actual intersection inclusion. -/
theorem manifoldSmoothSmallRestriction_intersection {k : ℕ} (a : Fin (k + 1) → ι) :
    ManifoldSmoothSmall.manifoldSmoothSmallRestriction E A X (fun i => (U i : Set X)) ≫
      smallManifoldSmoothIntersectionRestriction E X U A a =
        ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : DeRham.Comparison.SmoothCech.cechIntersection U a → X)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E))) := by
  rw [smallManifoldSmoothIntersectionRestriction, ← Category.assoc,
    ManifoldSmoothSmall.manifoldSmoothSmallRestriction_local]
  change ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : U (a 0) → X)
      (contMDiff_subtype_val (I := 𝓘(ℝ, E))) ≫
    ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Opens.inclusion (DeRham.Comparison.SmoothCech.cechIntersection_le U a 0))
      (contMDiff_inclusion (I := 𝓘(ℝ, E)) (DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)) = _
  rw [← ManifoldSmoothFunctor.manifoldSmoothPullback_comp]
  rfl

/-- The actual smooth singular presheaf gives a native Čech double complex. -/
abbrev manifoldSmoothCechDoubleComplex :
    HomologicalComplex₂ (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex U (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A)

/-- The two degrees index actual Čech tuples and actual smooth cochains. -/
@[simp]
theorem manifoldSmoothCechDoubleComplex_XX (k n : ℕ) :
    ((manifoldSmoothCechDoubleComplex E X U A).X k).X n =
      ModuleCat.of ℂ (DeRham.Comparison.SmoothCech.CechCochain (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U k) := rfl

/-- The horizontal differential is the existing signed Čech restriction sum. -/
@[simp]
theorem manifoldSmoothCechDoubleComplex_d_f (k n : ℕ) :
    ((manifoldSmoothCechDoubleComplex E X U A).d k (k + 1)).f n =
      ModuleCat.ofHom (DeRham.Comparison.SmoothCech.cechDelta (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U k) :=
  DeRham.Comparison.CechDoubleComplexFunctor.cechDoubleComplex_d_f U (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A) k n

/-- The vertical differential is the genuine smooth singular coboundary. -/
@[simp]
theorem manifoldSmoothCechDoubleComplex_X_d (k n : ℕ) :
    ((manifoldSmoothCechDoubleComplex E X U A).X k).d n (n + 1) =
      ModuleCat.ofHom
        (DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U ((ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A).d n (n + 1)) k) := rfl

/-- Its horizontal rows are exactly the checked smooth-cochain Čech rows. -/
@[simp]
theorem manifoldSmoothCechDoubleComplex_row (n : ℕ) :
    (manifoldSmoothCechDoubleComplex E X U A).flip.X n =
      DeRham.Comparison.SmoothCech.cechComplex (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U := rfl

/-- Every positive horizontal degree is exact, without a spatial cover
hypothesis. -/
theorem manifoldSmoothCechDoubleComplex_row_exact (k n : ℕ) :
    ((manifoldSmoothCechDoubleComplex E X U A).flip.X n).ExactAt (k + 1) :=
  ManifoldSmoothSmallCech.manifoldSmoothCochainCech_exactAt_succ E X U A n k

/-- The actual small-smooth row augmentations form a cochain map to the
zeroth Čech column. -/
def smallManifoldSmoothCechColumnAugmentation :
    ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X)) ⟶
      (manifoldSmoothCechDoubleComplex E X U A).X 0 where
  f n := ModuleCat.ofHom (ManifoldSmoothSmallCech.manifoldSmoothSmallCechStandardAugmentation E X U A n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [manifoldSmoothCechDoubleComplex_X_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact manifoldSmoothSmallCechStandardAugmentation_d E X U A i c

@[simp]
theorem smallManifoldSmoothCechColumnAugmentation_f (n : ℕ) :
    (smallManifoldSmoothCechColumnAugmentation E X U A).f n =
      ModuleCat.ofHom (ManifoldSmoothSmallCech.manifoldSmoothSmallCechStandardAugmentation E X U A n) := rfl

/-- Pairwise restrictions annihilate the actual small-smooth augmentation. -/
theorem smallManifoldSmoothCechColumnAugmentation_horizontal :
    smallManifoldSmoothCechColumnAugmentation E X U A ≫
      (manifoldSmoothCechDoubleComplex E X U A).d 0 1 = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    smallManifoldSmoothCechColumnAugmentation_f, manifoldSmoothCechDoubleComplex_d_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact ManifoldSmoothSmallCech.manifoldSmoothSmallCechStandardAugmentation_delta E X U A n c

/-- Global smooth cochains augment the same column by actual restriction. -/
def globalManifoldSmoothCechColumnAugmentation :
    ManifoldSmooth.manifoldSmoothCochains E A X ⟶ (manifoldSmoothCechDoubleComplex E X U A).X 0 :=
  ManifoldSmoothSmall.manifoldSmoothSmallRestriction E A X (fun i => (U i : Set X)) ≫
    smallManifoldSmoothCechColumnAugmentation E X U A

/-- Each component is exactly the smooth pullback along the corresponding
intersection inclusion. -/
theorem globalManifoldSmoothCechColumnAugmentation_apply (n : ℕ)
    (c : (ManifoldSmooth.manifoldSmoothCochains E A X).X n) (a : Fin 1 → ι) :
    ((globalManifoldSmoothCechColumnAugmentation E X U A).f n c) a =
      (ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : DeRham.Comparison.SmoothCech.cechIntersection U a → X)
        (contMDiff_subtype_val (I := 𝓘(ℝ, E)))).f n c := by
  have h := congrArg (fun f : ManifoldSmooth.manifoldSmoothCochains E A X ⟶
      ManifoldSmooth.manifoldSmoothCochains E A (DeRham.Comparison.SmoothCech.cechIntersection U a) => f.f n)
    (manifoldSmoothSmallRestriction_intersection E X U A a)
  exact ConcreteCategory.congr_hom h c

/-- Global smooth restrictions agree on pairwise intersections. -/
theorem globalManifoldSmoothCechColumnAugmentation_horizontal :
    globalManifoldSmoothCechColumnAugmentation E X U A ≫
      (manifoldSmoothCechDoubleComplex E X U A).d 0 1 = 0 := by
  rw [globalManifoldSmoothCechColumnAugmentation, Category.assoc,
    smallManifoldSmoothCechColumnAugmentation_horizontal, comp_zero]

/-- The genuine native total complex, including its native totalization signs. -/
abbrev manifoldSmoothCechTotal : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  (manifoldSmoothCechDoubleComplex E X U A).total (ComplexShape.up ℕ)

/-- Actual small smooth cochains augment the native total complex. -/
def smallManifoldSmoothCechAugmentation :
    ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X)) ⟶
      manifoldSmoothCechTotal E X U A :=
  DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (manifoldSmoothCechDoubleComplex E X U A)
    (smallManifoldSmoothCechColumnAugmentation E X U A)
    (smallManifoldSmoothCechColumnAugmentation_horizontal E X U A)

/-- Global smooth cochains augment the same actual native total complex. -/
def globalManifoldSmoothCechAugmentation :
    ManifoldSmooth.manifoldSmoothCochains E A X ⟶ manifoldSmoothCechTotal E X U A :=
  DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (manifoldSmoothCechDoubleComplex E X U A)
    (globalManifoldSmoothCechColumnAugmentation E X U A)
    (globalManifoldSmoothCechColumnAugmentation_horizontal E X U A)

@[simp]
theorem smallManifoldSmoothCechAugmentation_f (n : ℕ) :
    (smallManifoldSmoothCechAugmentation E X U A).f n =
      (smallManifoldSmoothCechColumnAugmentation E X U A).f n ≫
        (manifoldSmoothCechDoubleComplex E X U A).ιTotal
          (ComplexShape.up ℕ) 0 n n (by simp) := rfl

@[simp]
theorem globalManifoldSmoothCechAugmentation_f (n : ℕ) :
    (globalManifoldSmoothCechAugmentation E X U A).f n =
      (globalManifoldSmoothCechColumnAugmentation E X U A).f n ≫
        (manifoldSmoothCechDoubleComplex E X U A).ιTotal
          (ComplexShape.up ℕ) 0 n n (by simp) := rfl

/-- The total augmentation factors through the actual all-to-small
smooth cochain restriction. -/
theorem globalManifoldSmoothCechAugmentation_eq :
    globalManifoldSmoothCechAugmentation E X U A =
      ManifoldSmoothSmall.manifoldSmoothSmallRestriction E A X (fun i => (U i : Set X)) ≫
        smallManifoldSmoothCechAugmentation E X U A := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, smallManifoldSmoothCechAugmentation_f,
    globalManifoldSmoothCechAugmentation_f]
  exact Category.assoc _ _ _

/-- Restriction through the canonical top-open identification is the
direct smooth restriction to any actual open subset. -/
theorem manifoldSmoothPresheafTopIso_inv_restriction (W : Opens X) :
    (ManifoldSmoothSections.manifoldSmoothPresheafTopIso E X A).inv ≫
      ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E X A (homOfLE (show W ≤ ⊤ from le_top)) =
        ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : W → X)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E))) := by
  rw [ManifoldSmoothSections.manifoldSmoothPresheafTopIso_inv]
  change ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : (⊤ : Opens X) → X)
      (contMDiff_subtype_val (I := 𝓘(ℝ, E))) ≫
    ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Opens.inclusion (show W ≤ ⊤ from le_top))
      (contMDiff_inclusion (I := 𝓘(ℝ, E)) (show W ≤ ⊤ from le_top)) = _
  rw [← ManifoldSmoothFunctor.manifoldSmoothPullback_comp]
  rfl

/-- The actual global column augmentation agrees with the generic
presheaf-section augmentation under the canonical top-open identification. -/
theorem globalManifoldSmoothCechColumnAugmentation_eq_top :
    globalManifoldSmoothCechColumnAugmentation E X U A =
      (ManifoldSmoothSections.manifoldSmoothPresheafTopIso E X A).inv ≫
        DeRham.Comparison.CechComplexAugmentation.cechColumnAugmentation U ⊤ (fun _ => le_top)
          (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext a
  rw [globalManifoldSmoothCechColumnAugmentation_apply]
  exact (ConcreteCategory.congr_hom
    (congrArg (fun f : ManifoldSmooth.manifoldSmoothCochains E A X ⟶
      ManifoldSmooth.manifoldSmoothCochains E A (DeRham.Comparison.SmoothCech.cechIntersection U a) => f.f n)
      (manifoldSmoothPresheafTopIso_inv_restriction E X A (DeRham.Comparison.SmoothCech.cechIntersection U a))) c).symm

/-- The actual global total augmentation is the generic section
augmentation conjugated only by the canonical top-open cochain identification. -/
theorem globalManifoldSmoothCechAugmentation_eq_top :
    globalManifoldSmoothCechAugmentation E X U A =
      (ManifoldSmoothSections.manifoldSmoothPresheafTopIso E X A).inv ≫
        DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U ⊤ (fun _ => le_top)
          (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, globalManifoldSmoothCechAugmentation_f,
    DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation_f, globalManifoldSmoothCechColumnAugmentation_eq_top,
    HomologicalComplex.comp_f]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex
