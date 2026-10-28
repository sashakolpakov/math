import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Cech
import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechExact
import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainComparison
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison

/-! # Cech Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.CechComparison

noncomputable section

section

/-!
# ChernClass: exact rational singular Cech rows

This specializes the existing split-cover arguments to rational coefficients.
Set-cover coordinates and the small singular simplex maps are reused directly.
The actual augmentation is proved injective and exact.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech
section

variable {α ι : Type} (V : ι → Set α)

/-- The actual nerve augmentation induces restriction of functions to
degree-zero Čech cochains. -/
def coverCechCochainAugmentation (M : ModuleCat.{0} ℚ) :
    ModuleCat.of ℚ (α → M) ⟶ (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverCechCochains M V).X 0 :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α) M 0).inv ≫
    (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback M (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).hom).f 0

/-- Evaluation of the augmentation is precomposition with the actual
common-point projection of the Čech nerve. -/
theorem coverCechCochainAugmentation_evaluation (M : ModuleCat.{0} ℚ)
    (c : α → M) (z : (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋0⦌) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom
        (coverCechCochainAugmentation V M c) z =
      c (WidePullback.base (fun _ : Fin 1 => AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverProjection V) z) := by
  calc
    _ = (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α) M 0).hom
        ((AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α) M 0).inv c)
          ((AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).hom.app (op ⦋0⦌) z) :=
      AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback M (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).hom _ z
    _ = _ := by
      change ((AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α) M 0).toLinearEquiv
        (((AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α)
          M 0).toLinearEquiv).symm c)) _ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl

/-- The actual nerve augmentation lands in zero Čech cocycles. -/
theorem coverCechCochainAugmentation_d_zero (M : ModuleCat.{0} ℚ) (c : α → M) :
    (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverCechCochains M V).d 0 1 (coverCechCochainAugmentation V M c) = 0 := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 1).toLinearEquiv.injective
  funext z
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 1).hom _ z =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 1).hom 0 z
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_coboundary]
  have h (j : Fin 2) :
      (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom
          (coverCechCochainAugmentation V M c) ((AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ j z) =
        c (WidePullback.base (fun _ : Fin 2 => AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverProjection V) z) :=
    (coverCechCochainAugmentation_evaluation V M c _).trans
      (congrArg c (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechNerve_map_base V (SimplexCategory.δ j) z))
  rw [map_zero]
  change (∑ j : Fin 2, ((-1 : ℤ) ^ j.val) •
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom
      (coverCechCochainAugmentation V M c) ((AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ j z)) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul]
  exact (congrArg₂ (fun x y : M => x + -y) (h 0) (h 1)).trans (add_neg_cancel _)

end

section

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X)

variable (M : ModuleCat.{0} ℚ)

/-- The actual row cochain object is the product of singular cochain
modules on the corresponding finite open intersections. -/
def smallSingularCechDegreeEquiv (n k : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).X k ≃ₗ[ℚ]
      Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U k :=
  ((AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechDegreewiseFunctionIso X (fun i => (U i : Set X)) M n k).toLinearEquiv.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ => M)
      (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.smallSingularCechSimplexEquiv X U n k).symm)).trans
    ((LinearEquiv.piCurry ℚ (fun (a : Fin (k + 1) → ι)
      (_ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n) => M)).trans
        (LinearEquiv.piCongrRight (fun a =>
          (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M
            (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv.symm)))

/-- Evaluation of the cochain identification at an intersection simplex
is evaluation on its corresponding actual nerve simplex. -/
theorem smallSingularCechDegreeEquiv_evaluation (n k : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).X k)
    (a : Fin (k + 1) → ι)
    (σ : AlgebraicTopology.Cohomology.Singular.Basic.singularSimplices (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n) :
    (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).hom
        (smallSingularCechDegreeEquiv X U M n k c a) σ =
      (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechDegreewiseFunctionIso X (fun i => (U i : Set X)) M n k).hom c
        (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.smallSingularCechSimplexEquiv X U n k ⟨a, σ⟩) := by
  change ((AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv
      ((AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M
        (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv.symm
          (fun τ => (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechDegreewiseFunctionIso X
            (fun i => (U i : Set X)) M n k).hom c
              (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.smallSingularCechSimplexEquiv X U n k ⟨a, τ⟩)))) σ = _
  rw [LinearEquiv.apply_symm_apply]

/-- The degreewise identification preserves the existing signed Čech
differential, with its actual presheaf restriction maps. -/
theorem smallSingularCechDegreeEquiv_d (n k : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).X k) :
    smallSingularCechDegreeEquiv X U M n (k + 1)
        ((AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).d k (k + 1) c) =
      Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U k
        (smallSingularCechDegreeEquiv X U M n k c) := by
  funext a
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv.injective
  funext σ
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).hom _ σ =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M
        (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).hom _ σ
  rw [smallSingularCechDegreeEquiv_evaluation, AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains_d_apply,
    Cech.RationalCech.cechDelta_apply]
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun v : M => ((-1 : ℤ) ^ j.val) • v)
  change (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechDegreewiseFunctionIso X (fun i => (U i : Set X)) M n k).hom c
      ((AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X
        (fun i => (U i : Set X)) n)).left.map (SimplexCategory.δ j).op
          (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.smallSingularCechSimplexEquiv X U n (k + 1) ⟨a, σ⟩)) =
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj
      (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))) M n).hom
        ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback M (TopCat.toSSet.map ((Opens.toTopCat X).map
          (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove))))).f n
            (smallSingularCechDegreeEquiv X U M n k c (a ∘ j.succAbove))) σ
  rw [AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.smallSingularCechSimplexEquiv_map]
  let g : TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶
      TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (a ∘ j.succAbove)) :=
    (Opens.toTopCat X).map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove))
  exact (smallSingularCechDegreeEquiv_evaluation X U M n k c (a ∘ j.succAbove)
    ((TopCat.toSSet.map g).app (op ⦋n⦌) σ)).symm.trans
      (AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback M (TopCat.toSSet.map g)
        (smallSingularCechDegreeEquiv X U M n k c (a ∘ j.succAbove)) σ).symm

/-- Canonical isomorphism from the already checked small-singular Čech
row to the existing product-over-intersections Čech presheaf complex. -/
def smallSingularCechComparisonIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n ≅
      Cech.RationalCech.cechComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k => (smallSingularCechDegreeEquiv X U M n k).toModuleIso) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ConcreteCategory.ext_apply
      intro c
      rw [Cech.RationalCech.cechComplex_d]
      exact (smallSingularCechDegreeEquiv_d X U M n i c).symm)

@[simp]
theorem smallSingularCechComparisonIso_hom_f (n k : ℕ) :
    (smallSingularCechComparisonIso X U M n).hom.f k =
      ModuleCat.ofHom (smallSingularCechDegreeEquiv X U M n k).toLinearMap := rfl

/-- Positive-degree Čech exactness in the standard presheaf presentation,
transferred through the proved complex isomorphism. -/
theorem singularCochainCech_exactAt_succ (n k : ℕ) :
    (Cech.RationalCech.cechComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U).ExactAt
      (k + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains_exactAt_succ X (fun i => (U i : Set X)) M n k).isZero_homology.of_iso
      (((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (.up ℕ) (k + 1)).mapIso
        (smallSingularCechComparisonIso X U M n)).symm)

/-- Zeroth cohomology of the standard Čech row is the actual small
singular cochain module in the fixed singular degree. -/
def singularCochainCechHomologyZeroIso (n : ℕ) :
    (Cech.RationalCech.cechComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U).homology 0 ≅
      (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (.up ℕ) 0).mapIso
    (smallSingularCechComparisonIso X U M n)).symm ≪≫
      AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochainsHomologyZeroIso X (fun i => (U i : Set X)) M n

/-- Augmentation from actual small singular cochains to the actual
nerve row, using its common-simplex projection. -/
def smallSingularCechNerveAugmentation (n : ℕ) :
    (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n →ₗ[ℚ]
      (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).X 0 :=
  (coverCechCochainAugmentation
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M).hom.comp
      (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X (fun i => (U i : Set X)) n).hom.hom

theorem smallSingularCechNerveAugmentation_evaluation (n : ℕ)
    (c : (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n)
    (z : (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X
      (fun i => (U i : Set X)) n)).left _⦋0⦌) :
    (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechDegreewiseFunctionIso X (fun i => (U i : Set X)) M n 0).hom
        (smallSingularCechNerveAugmentation X U M n c) z =
      (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X (fun i => (U i : Set X)) n).hom c
        (WidePullback.base (fun _ : Fin 1 => AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverProjection
          (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n)) z) :=
  coverCechCochainAugmentation_evaluation _ M _ z

/-- Augmentation in the existing intersection presentation is the
actual singular restriction to each singleton intersection. -/
def smallSingularCechStandardAugmentation (n : ℕ) :
    (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n →ₗ[ℚ]
      Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0 where
  toFun c a :=
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat X).map
      (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)))).f n
        ((AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularLocalRestriction X (fun i => (U i : Set X)) M (a 0)).f n c)
  map_add' c d := by
    funext a
    simp only [map_add, Pi.add_apply]
  map_smul' a c := by
    funext b
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The canonical complex isomorphism preserves the actual restriction
augmentation, not merely an unspecified isomorphism on cohomology. -/
theorem smallSingularCechComparisonIso_augmentation (n : ℕ)
    (c : (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    (smallSingularCechComparisonIso X U M n).hom.f 0
        (smallSingularCechNerveAugmentation X U M n c) =
      smallSingularCechStandardAugmentation X U M n c := by
  funext a
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv.injective
  funext σ
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) n).hom
      (smallSingularCechDegreeEquiv X U M n 0
        (smallSingularCechNerveAugmentation X U M n c) a) σ = _
  rw [smallSingularCechDegreeEquiv_evaluation, smallSingularCechNerveAugmentation_evaluation,
    AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.smallSingularCechSimplexEquiv_base_local X U n 0 a σ 0]
  let g : TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ TopCat.of (U (a 0)) :=
    (Opens.toTopCat X).map (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0))
  exact (AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback M
    (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.localSmallSingularMap X (fun i => (U i : Set X)) (a 0)) c
      ((TopCat.toSSet.map g).app (op ⦋n⦌) σ)).symm.trans
        (AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback M (TopCat.toSSet.map g)
          ((AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularLocalRestriction X (fun i => (U i : Set X)) M (a 0)).f n c) σ).symm

/-- The actual standard augmentation lands in the kernel of the
existing degree-zero Čech differential. -/
theorem smallSingularCechStandardAugmentation_delta (n : ℕ)
    (c : (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0
      (smallSingularCechStandardAugmentation X U M n c) = 0 := by
  have h := smallSingularCechDegreeEquiv_d X U M n 0
    (smallSingularCechNerveAugmentation X U M n c)
  have ha : smallSingularCechDegreeEquiv X U M n 0
      (smallSingularCechNerveAugmentation X U M n c) =
        smallSingularCechStandardAugmentation X U M n c :=
    smallSingularCechComparisonIso_augmentation X U M n c
  rw [ha] at h
  have hz : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).d 0 1
      (smallSingularCechNerveAugmentation X U M n c) = 0 :=
    coverCechCochainAugmentation_d_zero _ M _
  rw [hz, map_zero] at h
  exact h.symm

/-- The nerve-row augmentation is a zero Čech cocycle on every small
singular cochain. -/
theorem smallSingularCechNerveAugmentation_d_zero (n : ℕ)
    (c : (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).d 0 1
      (smallSingularCechNerveAugmentation X U M n c) = 0 :=
  coverCechCochainAugmentation_d_zero
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M
    ((AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X (fun i => (U i : Set X)) n).hom c)

end

section

variable {α ι : Type} (V : ι → Set α) (M : ModuleCat.{0} ℚ)

/-- Čech tuple coordinates are determined by their labels and common point. -/
theorem coverCechTuple_ext {k : ℕ} {s t : AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.CoverCechTuple V k}
    (ha : s.1 = t.1) (hx : s.2.1 = t.2.1) : s = t := by
  apply Sigma.ext ha
  exact (Subtype.heq_iff_coe_eq (fun x => by rw [ha])).2 hx

/-- A vertex of the existing Čech nerve labelled by a local point. -/
def coverCechVertex (i : ι) (x : V i) : (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋0⦌ :=
  AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 0 ⟨fun _ => i, x.1, fun _ => x.2⟩

@[simp]
theorem coverCechVertex_base (i : ι) (x : V i) :
    WidePullback.base (fun _ : Fin 1 => AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverProjection V)
      (coverCechVertex V i x) = x.1 :=
  AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleToNerve_base V 0 ⟨fun _ => i, x.1, fun _ => x.2⟩

/-- An edge with the indicated two labels and a common point. -/
def coverCechEdge (i j : ι) (x : α) (hi : x ∈ V i) (hj : x ∈ V j) :
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋1⦌ :=
  AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 1 ⟨![i, j], x, Fin.forall_fin_two.2 ⟨hi, hj⟩⟩

@[simp]
theorem coverCechEdge_face_zero (i j : ι) (x : α) (hi : x ∈ V i) (hj : x ∈ V j) :
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ 0 (coverCechEdge V i j x hi hj) =
      coverCechVertex V j ⟨x, hj⟩ := by
  change (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left.map (SimplexCategory.δ (0 : Fin 2)).op
    (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 1 _) = AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 0 _
  rw [AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv_map]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 0)
  apply coverCechTuple_ext V
  · funext q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    rfl
  · rfl

@[simp]
theorem coverCechEdge_face_one (i j : ι) (x : α) (hi : x ∈ V i) (hj : x ∈ V j) :
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ 1 (coverCechEdge V i j x hi hj) =
      coverCechVertex V i ⟨x, hi⟩ := by
  change (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left.map (SimplexCategory.δ (1 : Fin 2)).op
    (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 1 _) = AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 0 _
  rw [AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv_map]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 0)
  apply coverCechTuple_ext V
  · funext q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    rfl
  · rfl

/-- Read a zero cochain as its family of local point-values. -/
def coverCechZeroFamily (b : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverCechCochains M V).X 0) : (i : ι) → V i → M :=
  fun i x => (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom b
    (coverCechVertex V i x)

/-- Every actual nerve vertex occurs in the local-family presentation. -/
theorem coverCechVertex_surjective (z : (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋0⦌) :
    ∃ (i : ι) (x : V i), coverCechVertex V i x = z := by
  obtain ⟨t, rfl⟩ := (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 0).surjective z
  refine ⟨t.1 0, ⟨t.2.1, t.2.2 0⟩, ?_⟩
  apply congrArg (AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison.coverCechTupleEquiv V 0)
  apply coverCechTuple_ext V
  · funext q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    rfl
  · rfl

/-- Local zero-cochain values determine the actual row cochain. -/
theorem coverCechZeroFamily_injective : Function.Injective (coverCechZeroFamily V M) := by
  intro b d h
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).toLinearEquiv.injective
  funext z
  obtain ⟨i, x, rfl⟩ := coverCechVertex_surjective V z
  exact congrFun (congrFun h i) x

/-- The actual augmentation is ordinary restriction on each local value. -/
@[simp]
theorem coverCechZeroFamily_augmentation (c : α → M) (i : ι) (x : V i) :
    coverCechZeroFamily V M (coverCechCochainAugmentation V M c) i x = c x := by
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom
    (coverCechCochainAugmentation V M c) (coverCechVertex V i x) = _
  rw [coverCechCochainAugmentation_evaluation, coverCechVertex_base]

/-- The zero-cocycle equation is equality of local values on overlaps. -/
theorem coverCechZeroFamily_matching (b : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverCechCochains M V).X 0)
    (hb : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverCechCochains M V).d 0 1 b = 0) :
    coverCechZeroFamily V M b ∈ AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverMatchingFunctions M V := by
  intro i j x hi hj
  have h := AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_coboundary (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M b
    (coverCechEdge V i j x hi hj)
  rw [hb, map_zero] at h
  change (0 : M) = ∑ q : Fin 2, ((-1 : ℤ) ^ q.val) •
    (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom b
      ((AlgebraicTopology.DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ q (coverCechEdge V i j x hi hj)) at h
  rw [Fin.sum_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    coverCechEdge_face_zero, coverCechEdge_face_one] at h
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg, coverCechZeroFamily] using h.symm)).symm

variable (hV : ∀ x, ∃ i, x ∈ V i)

include hV

/-- The actual augmentation of a set-cover Čech row is injective. -/
theorem coverCechCochainAugmentation_injective :
    Function.Injective (coverCechCochainAugmentation V M) := by
  intro c d h
  funext x
  obtain ⟨i, hi⟩ := hV x
  have he := congrArg (fun b => coverCechZeroFamily V M b i ⟨x, hi⟩) h
  exact (coverCechZeroFamily_augmentation V M c i ⟨x, hi⟩).symm.trans
    (he.trans (coverCechZeroFamily_augmentation V M d i ⟨x, hi⟩))

/-- Every zero Čech cocycle comes from the actual function augmentation. -/
theorem coverCechCochainAugmentation_preimage (b : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverCechCochains M V).X 0)
    (hb : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverCechCochains M V).d 0 1 b = 0) :
    ∃ c : α → M, coverCechCochainAugmentation V M c = b := by
  let family : AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverMatchingFunctions M V :=
    ⟨coverCechZeroFamily V M b, coverCechZeroFamily_matching V M b hb⟩
  refine ⟨(AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverFunctionGluingEquiv M V hV).symm family, ?_⟩
  apply coverCechZeroFamily_injective V M
  funext i x
  rw [coverCechZeroFamily_augmentation, AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverFunctionGluingEquiv_symm_apply]

/-- Exactness uses the canonical augmentation and canonical row differential. -/
theorem coverCechCochainAugmentation_exact :
    Function.Exact (coverCechCochainAugmentation V M) ((AlgebraicTopology.Cohomology.Singular.SmallCochainCech.coverCechCochains M V).d 0 1) := by
  intro b
  constructor
  · exact coverCechCochainAugmentation_preimage V M hV b
  · rintro ⟨c, rfl⟩
    exact coverCechCochainAugmentation_d_zero V M c

end

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X) (M : ModuleCat.{0} ℚ)

/-- The canonical augmentation into the standard singular Čech row is
injective, with no covering hypothesis beyond the definition of smallness. -/
theorem smallSingularCechStandardAugmentation_injective (n : ℕ) :
    Function.Injective (smallSingularCechStandardAugmentation X U M n) := by
  intro c d h
  apply (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X
    (fun i => (U i : Set X)) n).toLinearEquiv.injective
  apply coverCechCochainAugmentation_injective
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover_covers X (fun i => (U i : Set X)) n)
  apply (smallSingularCechDegreeEquiv X U M n 0).injective
  exact (smallSingularCechComparisonIso_augmentation X U M n c).trans
    (h.trans (smallSingularCechComparisonIso_augmentation X U M n d).symm)

/-- Every standard zero Čech cocycle has a preimage under the actual
small-singular restriction augmentation. -/
theorem smallSingularCechStandardAugmentation_preimage (n : ℕ)
    (c : Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0)
    (hc : Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0 c = 0) :
    ∃ b : (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n,
      smallSingularCechStandardAugmentation X U M n b = c := by
  let bN := (smallSingularCechDegreeEquiv X U M n 0).symm c
  have hbN : (AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).d 0 1 bN = 0 := by
    apply (smallSingularCechDegreeEquiv X U M n 1).injective
    calc
      _ = Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0
          (smallSingularCechDegreeEquiv X U M n 0 bN) :=
        smallSingularCechDegreeEquiv_d X U M n 0 bN
      _ = 0 := by
        change Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0
          ((smallSingularCechDegreeEquiv X U M n 0)
            ((smallSingularCechDegreeEquiv X U M n 0).symm c)) = 0
        rw [LinearEquiv.apply_symm_apply]
        exact hc
      _ = _ := (map_zero (smallSingularCechDegreeEquiv X U M n 1)).symm
  obtain ⟨f, hf⟩ := coverCechCochainAugmentation_preimage
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M
    (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover_covers X (fun i => (U i : Set X)) n) bN hbN
  let b := (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X
    (fun i => (U i : Set X)) n).inv f
  have hb : smallSingularCechNerveAugmentation X U M n b = bN := by
    change coverCechCochainAugmentation
      (AlgebraicTopology.DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M
        ((AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X
          (fun i => (U i : Set X)) n).toLinearEquiv
            ((AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X
              (fun i => (U i : Set X)) n).toLinearEquiv.symm f)) = bN
    rw [LinearEquiv.apply_symm_apply]
    exact hf
  refine ⟨b, ?_⟩
  calc
    _ = smallSingularCechDegreeEquiv X U M n 0
        (smallSingularCechNerveAugmentation X U M n b) :=
      (smallSingularCechComparisonIso_augmentation X U M n b).symm
    _ = smallSingularCechDegreeEquiv X U M n 0 bN :=
      congrArg (smallSingularCechDegreeEquiv X U M n 0) hb
    _ = c := (smallSingularCechDegreeEquiv X U M n 0).apply_symm_apply c

/-- The actual augmentation and actual standard Čech differential form
an exact pair, as required by the totalization argument. -/
theorem smallSingularCechStandardAugmentation_exact (n : ℕ) :
    Function.Exact (smallSingularCechStandardAugmentation X U M n)
      (Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0) := by
  intro c
  constructor
  · exact smallSingularCechStandardAugmentation_preimage X U M n c
  · rintro ⟨b, rfl⟩
    exact smallSingularCechStandardAugmentation_delta X U M n b

/-- Equivalent submodule statement for the same canonical maps. -/
theorem smallSingularCechStandardAugmentation_range (n : ℕ) :
    LinearMap.range (smallSingularCechStandardAugmentation X U M n) =
      LinearMap.ker (Cech.RationalCech.cechDelta
        (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0) :=
  (LinearMap.exact_iff.mp (smallSingularCechStandardAugmentation_exact X U M n)).symm

end RationalCech

end

/-!
# ChernClass: rational singular Cech comparison

Actual rational small cochains augment the rational Cech double complex.
The exact-row theorem proves that the augmentation is a quasi-isomorphism.
The proved rational small-singular comparison then identifies this total
cohomology with the existing rational singular cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace RationalCech
section

variable {ι : Type} (X : TopCat.{0})

variable (U : ι → Opens X) (M : ModuleCat.{0} ℚ)

/-- Actual restriction of cover-small cochains to a finite open intersection. -/
def smallSingularIntersectionRestriction {k : ℕ} (a : Fin (k + 1) → ι) :
    AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X)) ⟶
      AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) :=
  AlgebraicTopology.Cohomology.Singular.SmallCochainCech.smallSingularLocalRestriction X (fun i => (U i : Set X)) M (a 0) ≫
    AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M ((Opens.toTopCat X).map
      (homOfLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)))

/-- The standard row augmentation is exactly this cochain restriction
to each singleton intersection. -/
@[simp]
theorem smallSingularIntersectionRestriction_f (n : ℕ) (a : Fin 1 → ι)
    (c : (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    (smallSingularIntersectionRestriction X U M a).f n c =
      smallSingularCechStandardAugmentation X U M n c a := rfl

/-- The actual small-singular row augmentation commutes with the ordinary
singular coboundary in every internal degree. -/
theorem smallSingularCechStandardAugmentation_d (n : ℕ)
    (c : (AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).d n (n + 1)) 0
      (smallSingularCechStandardAugmentation X U M n c) =
        smallSingularCechStandardAugmentation X U M (n + 1)
          ((AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).d n (n + 1) c) := by
  funext a
  exact ConcreteCategory.congr_hom
    ((smallSingularIntersectionRestriction X U M a).comm n (n + 1)) c

/-- The two-step small restriction to an intersection equals the direct
ordinary singular restriction along its continuous inclusion. -/
theorem smallSingularRestriction_intersection {k : ℕ} (a : Fin (k + 1) → ι) :
    AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun i => (U i : Set X)) ≫
      smallSingularIntersectionRestriction X U M a =
        AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (show TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ X from
          TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) := by
  rw [smallSingularIntersectionRestriction, ← Category.assoc,
    AlgebraicTopology.Cohomology.Singular.CechDoubleComplex.smallSingularRestriction_local, ← AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_comp]
  rfl

/-- The genuine Čech double complex of the actual singular cochain presheaf.
The first degree is Čech degree and the second is singular cochain degree. -/
abbrev singularCechDoubleComplex :
    HomologicalComplex₂ (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  Cech.RationalCech.cechDoubleComplex U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X)

/-- Bidegree `(k,n)` consists of singular degree-`n` cochains on the actual
finite open intersections indexed by Čech `k`-tuples. -/
@[simp]
theorem singularCechDoubleComplex_XX (k n : ℕ) :
    ((singularCechDoubleComplex X U M).X k).X n =
      ModuleCat.of ℚ (Cech.RationalCech.CechCochain (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U k) := rfl

/-- The horizontal differential is the signed sum of actual restrictions. -/
@[simp]
theorem singularCechDoubleComplex_d_f (k n : ℕ) :
    ((singularCechDoubleComplex X U M).d k (k + 1)).f n =
      ModuleCat.ofHom (Cech.RationalCech.cechDelta (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U k) :=
  Cech.RationalCech.cechDoubleComplex_d_f U (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X) k n

/-- The vertical differential is the actual singular coboundary on each
intersection, with the totalization sign supplied by the native total complex. -/
@[simp]
theorem singularCechDoubleComplex_X_d (k n : ℕ) :
    ((singularCechDoubleComplex X U M).X k).d n (n + 1) =
      ModuleCat.ofHom
        (Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex M X).d n (n + 1)) k) := rfl

/-- The horizontal rows are exactly the previously checked singular Čech rows. -/
@[simp]
theorem singularCechDoubleComplex_row (n : ℕ) :
    (singularCechDoubleComplex X U M).flip.X n =
      Cech.RationalCech.cechComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U := rfl

/-- Every positive horizontal degree is exact, for any open family: the
augmentation resolves cochains on simplices small for that family. -/
theorem singularCechDoubleComplex_row_exact (k n : ℕ) :
    ((singularCechDoubleComplex X U M).flip.X n).ExactAt (k + 1) :=
  singularCochainCech_exactAt_succ X U M n k

/-- The actual small-cochain restrictions assemble into a cochain map to
column zero because they commute with the singular coboundary. -/
def smallSingularCechColumnAugmentation :
    AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X)) ⟶
      (singularCechDoubleComplex X U M).X 0 where
  f n := ModuleCat.ofHom (smallSingularCechStandardAugmentation X U M n)
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
      ModuleCat.ofHom (smallSingularCechStandardAugmentation X U M n) := rfl

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
  exact smallSingularCechStandardAugmentation_delta X U M n c

/-- Global singular cochains augment column zero by their actual restriction
through the small singular simplices. -/
def globalSingularCechColumnAugmentation :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X ⟶ (singularCechDoubleComplex X U M).X 0 :=
  AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun i => (U i : Set X)) ≫
    smallSingularCechColumnAugmentation X U M

/-- The global augmentation really is restriction along each intersection's
continuous inclusion into the original space. -/
theorem globalSingularCechColumnAugmentation_apply (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X).X n) (a : Fin 1 → ι) :
    ((globalSingularCechColumnAugmentation X U M).f n c) a =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback M (show TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ X from
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).f n c := by
  have h := congrArg (fun f : AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X ⟶
      AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M (TopCat.of (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)) => f.f n)
    (smallSingularRestriction_intersection X U M a)
  exact ConcreteCategory.congr_hom h c

/-- Global restrictions agree on pairwise intersections. -/
theorem globalSingularCechColumnAugmentation_horizontal :
    globalSingularCechColumnAugmentation X U M ≫
      (singularCechDoubleComplex X U M).d 0 1 = 0 := by
  rw [globalSingularCechColumnAugmentation, Category.assoc,
    smallSingularCechColumnAugmentation_horizontal, comp_zero]

/-- The native total complex of the genuine singular Čech double complex. -/
abbrev singularCechTotal : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  (singularCechDoubleComplex X U M).total (ComplexShape.up ℕ)

/-- The small-cochain augmentation into the actual native total complex. -/
def smallSingularCechAugmentation :
    AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X)) ⟶ singularCechTotal X U M :=
  AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (singularCechDoubleComplex X U M)
    (smallSingularCechColumnAugmentation X U M)
    (smallSingularCechColumnAugmentation_horizontal X U M)

/-- The global singular augmentation into the same native total complex. -/
def globalSingularCechAugmentation : AlgebraicTopology.Cohomology.Singular.Basic.singularCochains M X ⟶ singularCechTotal X U M :=
  AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex.augmentationToTotal (singularCechDoubleComplex X U M)
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
      AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularRestriction M X (fun i => (U i : Set X)) ≫
        smallSingularCechAugmentation X U M := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, smallSingularCechAugmentation_f,
    globalSingularCechAugmentation_f]
  exact Category.assoc _ _ _

end

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X) (M : ModuleCat.{0} ℚ)

/-- Restriction of small cochains into the zeroth Čech column is injective
in each genuine singular degree. -/
theorem smallSingularCechColumnAugmentation_injective (n : ℕ) :
    Function.Injective ((smallSingularCechColumnAugmentation X U M).f n) :=
  smallSingularCechStandardAugmentation_injective X U M n

/-- The kernel of the first actual horizontal differential is precisely
the image of the small-singular augmentation. -/
theorem smallSingularCechColumnAugmentation_exact (n : ℕ) :
    Function.Exact ((smallSingularCechColumnAugmentation X U M).f n)
      (((singularCechDoubleComplex X U M).d 0 1).f n) := by
  rw [smallSingularCechColumnAugmentation_f, singularCechDoubleComplex_d_f]
  exact smallSingularCechStandardAugmentation_exact X U M n

/-- The canonical augmentation from actual small singular cochains to the
native Čech total complex is a quasi-isomorphism for every open family. -/
theorem smallSingularCechAugmentation_quasiIso :
    QuasiIso (smallSingularCechAugmentation X U M) :=
  AlgebraicTopology.DeRham.Comparison.DoubleComplexComparison.DoubleComplex.augmentationToTotal_quasiIso (singularCechDoubleComplex X U M)
    (smallSingularCechColumnAugmentation X U M)
    (smallSingularCechColumnAugmentation_horizontal X U M)
    (smallSingularCechColumnAugmentation_injective X U M)
    (smallSingularCechColumnAugmentation_exact X U M)
    (singularCechDoubleComplex_row_exact X U M)

/-- The induced isomorphism is the one from the actual small-cochain
restriction augmentation. -/
def smallSingularCechCohomologyIso (n : ℕ) :
    AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCohomology M X (fun i => (U i : Set X)) n ≅
      (singularCechTotal X U M).homology n := by
  letI := smallSingularCechAugmentation_quasiIso X U M
  exact isoOfQuasiIsoAt (smallSingularCechAugmentation X U M) n

@[simp]
theorem smallSingularCechCohomologyIso_hom (n : ℕ) :
    (smallSingularCechCohomologyIso X U M n).hom =
      HomologicalComplex.homologyMap (smallSingularCechAugmentation X U M) n := rfl

/-- On an actual open cover, ordinary rational singular cochains map
quasi-isomorphically to the actual Čech total complex by restriction. -/
theorem rationalGlobalSingularCechAugmentation_quasiIso
    (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) := by
  have := AlgebraicTopology.Cohomology.Singular.SmallCochainComparison.rationalSmallSingularRestriction_quasiIso X (fun i => (U i : Set X))
    (fun i => (U i).isOpen) hcover
  have := smallSingularCechAugmentation_quasiIso X U (ModuleCat.of ℚ ℚ)
  rw [globalSingularCechAugmentation_eq]
  infer_instance

/-- The ordinary rational singular cohomology of a space is canonically
the cohomology of the singular Čech total complex for any actual open cover. -/
def singularCechCohomologyIso (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n ≅
      (singularCechTotal X U (ModuleCat.of ℚ ℚ)).homology n := by
  letI := rationalGlobalSingularCechAugmentation_quasiIso X U hcover
  exact isoOfQuasiIsoAt (globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) n

/-- The displayed cohomology isomorphism is induced by the genuine global
restriction augmentation, fixing its mathematical meaning. -/
@[simp]
theorem singularCechCohomologyIso_hom (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (singularCechCohomologyIso X U hcover n).hom =
      HomologicalComplex.homologyMap
        (globalSingularCechAugmentation X U (ModuleCat.of ℚ ℚ)) n := rfl

/-- On cohomology the global augmentation factors through the same actual
small-simplex restriction and its canonical totalization isomorphism. -/
theorem globalSingularCechAugmentation_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (globalSingularCechAugmentation X U M) n =
      AlgebraicTopology.DeRham.Comparison.SmallSingularCochains.smallSingularCohomologyRestriction M X (fun i => (U i : Set X)) n ≫
        (smallSingularCechCohomologyIso X U M n).hom := by
  rw [globalSingularCechAugmentation_eq, HomologicalComplex.homologyMap_comp]
  rfl

end RationalCech

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.CechComparison
