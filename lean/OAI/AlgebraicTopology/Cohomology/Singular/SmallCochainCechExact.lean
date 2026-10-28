import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison
import Mathlib.Algebra.Exact.Basic

/-! # Small Cochain Cech Exact -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechExact

noncomputable section

/-!
# Exactness of the actual small-singular Čech augmentation

The degree-zero cocycle equation on each pair of cover members gives
compatible local simplex values. The proved function-gluing equivalence
then constructs a preimage under the actual augmentation. This proves
injectivity and exactness of the canonical augmentation used in the
standard intersection Čech complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section SetCover

variable {α ι : Type} (V : ι → Set α) (M : ModuleCat.{0} ℂ)

/-- Čech tuple coordinates are determined by their labels and common point. -/
theorem coverCechTuple_ext {k : ℕ} {s t : SmallCochainCechComparison.CoverCechTuple V k}
    (ha : s.1 = t.1) (hx : s.2.1 = t.2.1) : s = t := by
  apply Sigma.ext ha
  exact (Subtype.heq_iff_coe_eq (fun x => by rw [ha])).2 hx

/-- A vertex of the existing Čech nerve labelled by a local point. -/
def coverCechVertex (i : ι) (x : V i) : (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋0⦌ :=
  SmallCochainCechComparison.coverCechTupleEquiv V 0 ⟨fun _ => i, x.1, fun _ => x.2⟩

@[simp]
theorem coverCechVertex_base (i : ι) (x : V i) :
    WidePullback.base (fun _ : Fin 1 => DeRham.Comparison.CechCoverRows.coverProjection V)
      (coverCechVertex V i x) = x.1 :=
  SmallCochainCechComparison.coverCechTupleToNerve_base V 0 ⟨fun _ => i, x.1, fun _ => x.2⟩

/-- An edge with the indicated two labels and a common point. -/
def coverCechEdge (i j : ι) (x : α) (hi : x ∈ V i) (hj : x ∈ V j) :
    (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋1⦌ :=
  SmallCochainCechComparison.coverCechTupleEquiv V 1 ⟨![i, j], x, Fin.forall_fin_two.2 ⟨hi, hj⟩⟩

@[simp]
theorem coverCechEdge_face_zero (i j : ι) (x : α) (hi : x ∈ V i) (hj : x ∈ V j) :
    (DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ 0 (coverCechEdge V i j x hi hj) =
      coverCechVertex V j ⟨x, hj⟩ := by
  change (DeRham.Comparison.CechCoverRows.coverCechNerve V).left.map (SimplexCategory.δ (0 : Fin 2)).op
    (SmallCochainCechComparison.coverCechTupleEquiv V 1 _) = SmallCochainCechComparison.coverCechTupleEquiv V 0 _
  rw [SmallCochainCechComparison.coverCechTupleEquiv_map]
  apply congrArg (SmallCochainCechComparison.coverCechTupleEquiv V 0)
  apply coverCechTuple_ext V
  · funext q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    rfl
  · rfl

@[simp]
theorem coverCechEdge_face_one (i j : ι) (x : α) (hi : x ∈ V i) (hj : x ∈ V j) :
    (DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ 1 (coverCechEdge V i j x hi hj) =
      coverCechVertex V i ⟨x, hi⟩ := by
  change (DeRham.Comparison.CechCoverRows.coverCechNerve V).left.map (SimplexCategory.δ (1 : Fin 2)).op
    (SmallCochainCechComparison.coverCechTupleEquiv V 1 _) = SmallCochainCechComparison.coverCechTupleEquiv V 0 _
  rw [SmallCochainCechComparison.coverCechTupleEquiv_map]
  apply congrArg (SmallCochainCechComparison.coverCechTupleEquiv V 0)
  apply coverCechTuple_ext V
  · funext q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    rfl
  · rfl

/-- Read a zero cochain as its family of local point-values. -/
def coverCechZeroFamily (b : (SmallCochainCech.coverCechCochains M V).X 0) : (i : ι) → V i → M :=
  fun i x => (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom b
    (coverCechVertex V i x)

/-- Every actual nerve vertex occurs in the local-family presentation. -/
theorem coverCechVertex_surjective (z : (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋0⦌) :
    ∃ (i : ι) (x : V i), coverCechVertex V i x = z := by
  obtain ⟨t, rfl⟩ := (SmallCochainCechComparison.coverCechTupleEquiv V 0).surjective z
  refine ⟨t.1 0, ⟨t.2.1, t.2.2 0⟩, ?_⟩
  apply congrArg (SmallCochainCechComparison.coverCechTupleEquiv V 0)
  apply coverCechTuple_ext V
  · funext q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    rfl
  · rfl

/-- Local zero-cochain values determine the actual row cochain. -/
theorem coverCechZeroFamily_injective : Function.Injective (coverCechZeroFamily V M) := by
  intro b d h
  apply (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).toLinearEquiv.injective
  funext z
  obtain ⟨i, x, rfl⟩ := coverCechVertex_surjective V z
  exact congrFun (congrFun h i) x

/-- The actual augmentation is ordinary restriction on each local value. -/
@[simp]
theorem coverCechZeroFamily_augmentation (c : α → M) (i : ι) (x : V i) :
    coverCechZeroFamily V M (SmallCochainCechComparison.coverCechCochainAugmentation V M c) i x = c x := by
  change (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom
    (SmallCochainCechComparison.coverCechCochainAugmentation V M c) (coverCechVertex V i x) = _
  rw [SmallCochainCechComparison.coverCechCochainAugmentation_evaluation, coverCechVertex_base]

/-- The zero-cocycle equation is equality of local values on overlaps. -/
theorem coverCechZeroFamily_matching (b : (SmallCochainCech.coverCechCochains M V).X 0)
    (hb : (SmallCochainCech.coverCechCochains M V).d 0 1 b = 0) :
    coverCechZeroFamily V M b ∈ SmallCochainCech.coverMatchingFunctions M V := by
  intro i j x hi hj
  have h := Formulas.degreewiseFunctionIso_coboundary (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M b
    (coverCechEdge V i j x hi hj)
  rw [hb, map_zero] at h
  change (0 : M) = ∑ q : Fin 2, ((-1 : ℤ) ^ q.val) •
    (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom b
      ((DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ q (coverCechEdge V i j x hi hj)) at h
  rw [Fin.sum_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    coverCechEdge_face_zero, coverCechEdge_face_one] at h
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg, coverCechZeroFamily] using h.symm)).symm

variable (hV : ∀ x, ∃ i, x ∈ V i)

include hV

/-- The actual augmentation of a set-cover Čech row is injective. -/
theorem coverCechCochainAugmentation_injective :
    Function.Injective (SmallCochainCechComparison.coverCechCochainAugmentation V M) := by
  intro c d h
  funext x
  obtain ⟨i, hi⟩ := hV x
  have he := congrArg (fun b => coverCechZeroFamily V M b i ⟨x, hi⟩) h
  exact (coverCechZeroFamily_augmentation V M c i ⟨x, hi⟩).symm.trans
    (he.trans (coverCechZeroFamily_augmentation V M d i ⟨x, hi⟩))

/-- Every zero Čech cocycle comes from the actual function augmentation. -/
theorem coverCechCochainAugmentation_preimage (b : (SmallCochainCech.coverCechCochains M V).X 0)
    (hb : (SmallCochainCech.coverCechCochains M V).d 0 1 b = 0) :
    ∃ c : α → M, SmallCochainCechComparison.coverCechCochainAugmentation V M c = b := by
  let family : SmallCochainCech.coverMatchingFunctions M V :=
    ⟨coverCechZeroFamily V M b, coverCechZeroFamily_matching V M b hb⟩
  refine ⟨(SmallCochainCech.coverFunctionGluingEquiv M V hV).symm family, ?_⟩
  apply coverCechZeroFamily_injective V M
  funext i x
  rw [coverCechZeroFamily_augmentation, SmallCochainCech.coverFunctionGluingEquiv_symm_apply]

/-- Exactness uses the canonical augmentation and canonical row differential. -/
theorem coverCechCochainAugmentation_exact :
    Function.Exact (SmallCochainCechComparison.coverCechCochainAugmentation V M) ((SmallCochainCech.coverCechCochains M V).d 0 1) := by
  intro b
  constructor
  · exact coverCechCochainAugmentation_preimage V M hV b
  · rintro ⟨c, rfl⟩
    exact SmallCochainCechComparison.coverCechCochainAugmentation_d_zero V M c

end SetCover

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X) (M : ModuleCat.{0} ℂ)

/-- The canonical augmentation into the standard singular Čech row is
injective, with no covering hypothesis beyond the definition of smallness. -/
theorem smallSingularCechStandardAugmentation_injective (n : ℕ) :
    Function.Injective (SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M n) := by
  intro c d h
  apply (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X
    (fun i => (U i : Set X)) n).toLinearEquiv.injective
  apply coverCechCochainAugmentation_injective
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover_covers X (fun i => (U i : Set X)) n)
  apply (SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0).injective
  exact (SmallCochainCechComparison.smallSingularCechComparisonIso_augmentation X U M n c).trans
    (h.trans (SmallCochainCechComparison.smallSingularCechComparisonIso_augmentation X U M n d).symm)

/-- Every standard zero Čech cocycle has a preimage under the actual
small-singular restriction augmentation. -/
theorem smallSingularCechStandardAugmentation_preimage (n : ℕ)
    (c : DeRham.Comparison.SmoothCech.CechCochain (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0)
    (hc : DeRham.Comparison.SmoothCech.cechDelta (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0 c = 0) :
    ∃ b : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n,
      SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M n b = c := by
  let bN := (SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0).symm c
  have hbN : (SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).d 0 1 bN = 0 := by
    apply (SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 1).injective
    calc
      _ = DeRham.Comparison.SmoothCech.cechDelta (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0
          (SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0 bN) :=
        SmallCochainCechComparison.smallSingularCechDegreeEquiv_d X U M n 0 bN
      _ = 0 := by
        change DeRham.Comparison.SmoothCech.cechDelta (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0
          ((SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0)
            ((SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0).symm c)) = 0
        rw [LinearEquiv.apply_symm_apply]
        exact hc
      _ = _ := (map_zero (SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 1)).symm
  obtain ⟨f, hf⟩ := coverCechCochainAugmentation_preimage
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover_covers X (fun i => (U i : Set X)) n) bN hbN
  let b := (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X
    (fun i => (U i : Set X)) n).inv f
  have hb : SmallCochainCechComparison.smallSingularCechNerveAugmentation X U M n b = bN := by
    change SmallCochainCechComparison.coverCechCochainAugmentation
      (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M
        ((DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X
          (fun i => (U i : Set X)) n).toLinearEquiv
            ((DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X
              (fun i => (U i : Set X)) n).toLinearEquiv.symm f)) = bN
    rw [LinearEquiv.apply_symm_apply]
    exact hf
  refine ⟨b, ?_⟩
  calc
    _ = SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0
        (SmallCochainCechComparison.smallSingularCechNerveAugmentation X U M n b) :=
      (SmallCochainCechComparison.smallSingularCechComparisonIso_augmentation X U M n b).symm
    _ = SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0 bN :=
      congrArg (SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0) hb
    _ = c := (SmallCochainCechComparison.smallSingularCechDegreeEquiv X U M n 0).apply_symm_apply c

/-- The actual augmentation and actual standard Čech differential form
an exact pair, as required by the totalization argument. -/
theorem smallSingularCechStandardAugmentation_exact (n : ℕ) :
    Function.Exact (SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M n)
      (DeRham.Comparison.SmoothCech.cechDelta (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0) := by
  intro c
  constructor
  · exact smallSingularCechStandardAugmentation_preimage X U M n c
  · rintro ⟨b, rfl⟩
    exact SmallCochainCechComparison.smallSingularCechStandardAugmentation_delta X U M n b

/-- Equivalent submodule statement for the same canonical maps. -/
theorem smallSingularCechStandardAugmentation_range (n : ℕ) :
    LinearMap.range (SmallCochainCechComparison.smallSingularCechStandardAugmentation X U M n) =
      LinearMap.ker (DeRham.Comparison.SmoothCech.cechDelta
        (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0) :=
  (LinearMap.exact_iff.mp (smallSingularCechStandardAugmentation_exact X U M n)).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechExact
