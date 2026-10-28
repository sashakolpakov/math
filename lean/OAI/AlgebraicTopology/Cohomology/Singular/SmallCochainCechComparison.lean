import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCech
import OAI.AlgebraicTopology.DeRham.Comparison.SingularPresheaf
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothCech
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # Small Cochain Cech Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison

noncomputable section

/-!
# Comparing the two actual singular Čech row presentations

The Čech nerve of the cover of small simplices is identified with tuples
of cover indices together with a singular simplex in their intersection.
This identifies its cochains with the existing Čech complex of the
singular-cochain presheaf, including its differential and augmentation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section SetCoverCoordinates

variable {α ι : Type} (V : ι → Set α)

/-- Coordinates for a simplex of the actual Čech nerve: a tuple of cover
indices and a point in their common intersection. -/
abbrev CoverCechTuple (k : ℕ) :=
  Σ a : Fin (k + 1) → ι, {x : α // ∀ j, x ∈ V (a j)}

/-- The universal wide-pullback lift of a tuple and its common point. -/
def coverCechTupleToNerve (k : ℕ) :
    CoverCechTuple V k ⟶ (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋k⦌ :=
  WidePullback.lift (arrows := fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V)
    (TypeCat.ofHom (fun t => t.2.1))
    (fun j => TypeCat.ofHom (fun t => ⟨t.1 j, t.2.1, t.2.2 j⟩))
    (fun _ => rfl)

@[simp]
theorem coverCechTupleToNerve_base (k : ℕ) (t : CoverCechTuple V k) :
    WidePullback.base (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V)
        (coverCechTupleToNerve V k t) = t.2.1 := by
  change (coverCechTupleToNerve V k ≫
    WidePullback.base (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V)) t = _
  rw [coverCechTupleToNerve, WidePullback.lift_base]
  rfl

@[simp]
theorem coverCechTupleToNerve_π (k : ℕ) (t : CoverCechTuple V k) (j : Fin (k + 1)) :
    WidePullback.π (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j
        (coverCechTupleToNerve V k t) = ⟨t.1 j, t.2.1, t.2.2 j⟩ := by
  change (coverCechTupleToNerve V k ≫
    WidePullback.π (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j) t = _
  rw [coverCechTupleToNerve, WidePullback.lift_π]
  rfl

/-- Read the cover labels and the common point from the actual nerve. -/
def coverCechTupleFromNerve (k : ℕ)
    (z : (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋k⦌) : CoverCechTuple V k :=
  ⟨fun j => (WidePullback.π
      (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j z).1,
    WidePullback.base (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) z,
    fun j => by
      have h := ConcreteCategory.congr_hom
        (WidePullback.π_arrow (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j) z
      exact h ▸ (WidePullback.π
        (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j z).2.2⟩

/-- The coordinates are equivalent to the actual universal-limit Čech
nerve, with no replacement simplicial object. -/
def coverCechTupleEquiv (k : ℕ) :
    CoverCechTuple V k ≃ (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋k⦌ where
  toFun := coverCechTupleToNerve V k
  invFun := coverCechTupleFromNerve V k
  left_inv t := by
    have ha : (coverCechTupleFromNerve V k (coverCechTupleToNerve V k t)).1 = t.1 := by
      funext j
      exact congrArg Sigma.fst (coverCechTupleToNerve_π V k t j)
    apply Sigma.ext ha
    apply (Subtype.heq_iff_coe_eq (fun x => by rw [ha])).2
    exact coverCechTupleToNerve_base V k t
  right_inv z := by
    apply Types.limit_ext
    intro j
    cases j with
    | none => exact coverCechTupleToNerve_base V k _
    | some j =>
      change WidePullback.π (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j
        (coverCechTupleToNerve V k (coverCechTupleFromNerve V k z)) = _
      rw [coverCechTupleToNerve_π]
      dsimp only [coverCechTupleFromNerve]
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      apply Subtype.ext
      exact (ConcreteCategory.congr_hom
        (WidePullback.π_arrow (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j) z).symm

/-- Every simplicial operator on the Čech nerve leaves the common point
unchanged. -/
theorem coverCechNerve_map_base {k l : ℕ} (f : ⦋k⦌ ⟶ ⦋l⦌)
    (z : (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋l⦌) :
    WidePullback.base (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V)
        ((DeRham.Comparison.CechCoverRows.coverCechNerve V).left.map f.op z) =
      WidePullback.base (fun _ : Fin (l + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) z := by
  exact ConcreteCategory.congr_hom
    (WidePullback.lift_base
      (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V)
      (WidePullback.base (fun _ : Fin (l + 1) => DeRham.Comparison.CechCoverRows.coverProjection V))
      (fun j : Fin (k + 1) => WidePullback.π
        (fun _ : Fin (l + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) (f.toOrderHom j))
      (by intro j; exact WidePullback.π_arrow _ _)) z

/-- Every simplicial operator selects the corresponding cover labels. -/
theorem coverCechNerve_map_π {k l : ℕ} (f : ⦋k⦌ ⟶ ⦋l⦌)
    (z : (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋l⦌) (j : Fin (k + 1)) :
    WidePullback.π (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j
        ((DeRham.Comparison.CechCoverRows.coverCechNerve V).left.map f.op z) =
      WidePullback.π (fun _ : Fin (l + 1) => DeRham.Comparison.CechCoverRows.coverProjection V)
        (f.toOrderHom j) z := by
  exact ConcreteCategory.congr_hom
    (WidePullback.lift_π
      (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V)
      (WidePullback.base (fun _ : Fin (l + 1) => DeRham.Comparison.CechCoverRows.coverProjection V))
      (fun q : Fin (k + 1) => WidePullback.π
        (fun _ : Fin (l + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) (f.toOrderHom q))
      (by intro q; exact WidePullback.π_arrow _ _) j) z

/-- The coordinate equivalence intertwines the actual simplicial maps
with precomposition of tuples. -/
theorem coverCechTupleEquiv_map {k l : ℕ} (f : ⦋k⦌ ⟶ ⦋l⦌)
    (t : CoverCechTuple V l) :
    (DeRham.Comparison.CechCoverRows.coverCechNerve V).left.map f.op (coverCechTupleEquiv V l t) =
      coverCechTupleEquiv V k
        ⟨t.1 ∘ f.toOrderHom, t.2.1, fun j => t.2.2 (f.toOrderHom j)⟩ := by
  apply Types.limit_ext
  intro j
  cases j with
  | none =>
    change WidePullback.base (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) _ =
      WidePullback.base (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) _
    rw [coverCechNerve_map_base]
    exact (coverCechTupleToNerve_base V l t).trans
      (coverCechTupleToNerve_base V k
        ⟨t.1 ∘ f.toOrderHom, t.2.1, fun j => t.2.2 (f.toOrderHom j)⟩).symm
  | some j =>
    change WidePullback.π (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j _ =
      WidePullback.π (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection V) j _
    rw [coverCechNerve_map_π]
    exact (coverCechTupleToNerve_π V l t (f.toOrderHom j)).trans
      (coverCechTupleToNerve_π V k
        ⟨t.1 ∘ f.toOrderHom, t.2.1, fun q => t.2.2 (f.toOrderHom q)⟩ j).symm

/-- The actual nerve augmentation induces restriction of functions to
degree-zero Čech cochains. -/
def coverCechCochainAugmentation (M : ModuleCat.{0} ℂ) :
    ModuleCat.of ℂ (α → M) ⟶ (SmallCochainCech.coverCechCochains M V).X 0 :=
  (Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α) M 0).inv ≫
    (Functor.simplicialPullback M (DeRham.Comparison.CechCoverRows.coverCechNerve V).hom).f 0

/-- Evaluation of the augmentation is precomposition with the actual
common-point projection of the Čech nerve. -/
theorem coverCechCochainAugmentation_evaluation (M : ModuleCat.{0} ℂ)
    (c : α → M) (z : (DeRham.Comparison.CechCoverRows.coverCechNerve V).left _⦋0⦌) :
    (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom
        (coverCechCochainAugmentation V M c) z =
      c (WidePullback.base (fun _ : Fin 1 => DeRham.Comparison.CechCoverRows.coverProjection V) z) := by
  calc
    _ = (Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α) M 0).hom
        ((Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α) M 0).inv c)
          ((DeRham.Comparison.CechCoverRows.coverCechNerve V).hom.app (op ⦋0⦌) z) :=
      Formulas.degreewiseFunctionIso_pullback M (DeRham.Comparison.CechCoverRows.coverCechNerve V).hom _ z
    _ = _ := by
      change ((Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α) M 0).toLinearEquiv
        (((Coefficients.degreewiseFunctionIso ((SimplicialObject.const (Type)).obj α)
          M 0).toLinearEquiv).symm c)) _ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl

/-- The actual nerve augmentation lands in zero Čech cocycles. -/
theorem coverCechCochainAugmentation_d_zero (M : ModuleCat.{0} ℂ) (c : α → M) :
    (SmallCochainCech.coverCechCochains M V).d 0 1 (coverCechCochainAugmentation V M c) = 0 := by
  apply (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 1).toLinearEquiv.injective
  funext z
  change (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 1).hom _ z =
    (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 1).hom 0 z
  rw [Formulas.degreewiseFunctionIso_coboundary]
  have h (j : Fin 2) :
      (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom
          (coverCechCochainAugmentation V M c) ((DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ j z) =
        c (WidePullback.base (fun _ : Fin 2 => DeRham.Comparison.CechCoverRows.coverProjection V) z) :=
    (coverCechCochainAugmentation_evaluation V M c _).trans
      (congrArg c (coverCechNerve_map_base V (SimplexCategory.δ j) z))
  rw [map_zero]
  change (∑ j : Fin 2, ((-1 : ℤ) ^ j.val) •
    (Coefficients.degreewiseFunctionIso (DeRham.Comparison.CechCoverRows.coverCechNerve V).left M 0).hom
      (coverCechCochainAugmentation V M c) ((DeRham.Comparison.CechCoverRows.coverCechNerve V).left.δ j z)) = 0
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul]
  exact (congrArg₂ (fun x y : M => x + -y) (h 0) (h 1)).trans (add_neg_cancel _)

end SetCoverCoordinates

variable {ι : Type} (X : TopCat.{0}) (U : ι → Opens X)

/-- A simplex in a finite open intersection is exactly a small ambient
simplex lying in every open set named by the tuple. -/
def intersectionSmallSingularSimplexEquiv (n : ℕ) {k : ℕ}
    (a : Fin (k + 1) → ι) :
    Basic.singularSimplices (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n ≃
      {σ : DeRham.Comparison.CechCoverRows.SmallSingularSimplex X (fun i => (U i : Set X)) n //
        ∀ j, σ ∈ DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X
          (fun i => (U i : Set X)) n (a j)} :=
  (SmallCochainCech.singularSimplexSubtypeEquiv X (DeRham.Comparison.SmoothCech.cechIntersection U a : Set X) n).trans
    { toFun := fun σ =>
        ⟨⟨σ.1, ⟨a 0, fun _y hy => DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 (σ.2 hy)⟩⟩,
          fun j _y hy => DeRham.Comparison.SmoothCech.cechIntersection_le U a j (σ.2 hy)⟩
      invFun := fun σ =>
        ⟨σ.1.1, fun y hy => (DeRham.Comparison.SmoothCech.mem_cechIntersection U a y).2
          (fun j => σ.2 j hy)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The existing Čech nerve of small singular simplices is degreewise
the disjoint union of actual singular simplices in finite open intersections. -/
def smallSingularCechSimplexEquiv (n k : ℕ) :
    (Σ a : Fin (k + 1) → ι,
      Basic.singularSimplices (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n) ≃
        (DeRham.Comparison.CechCoverRows.coverCechNerve (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X
          (fun i => (U i : Set X)) n)).left _⦋k⦌ :=
  (Equiv.sigmaCongrRight (fun a => intersectionSmallSingularSimplexEquiv X U n a)).trans
    (coverCechTupleEquiv (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X
      (fun i => (U i : Set X)) n) k)

/-- The simplex identification sends actual Čech faces and degeneracies
to the ordinary inclusions between their open intersection domains. -/
theorem smallSingularCechSimplexEquiv_map (n : ℕ) {k l : ℕ}
    (f : ⦋k⦌ ⟶ ⦋l⦌) (a : Fin (l + 1) → ι)
    (σ : Basic.singularSimplices (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n) :
    (DeRham.Comparison.CechCoverRows.coverCechNerve (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X
      (fun i => (U i : Set X)) n)).left.map f.op
        (smallSingularCechSimplexEquiv X U n l ⟨a, σ⟩) =
      smallSingularCechSimplexEquiv X U n k
        ⟨a ∘ f.toOrderHom,
          (TopCat.toSSet.map ((Opens.toTopCat X).map
            (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f.toOrderHom)))).app
              (op ⦋n⦌) σ⟩ := by
  change (DeRham.Comparison.CechCoverRows.coverCechNerve _).left.map f.op
      (coverCechTupleEquiv _ l ⟨a, intersectionSmallSingularSimplexEquiv X U n a σ⟩) =
    coverCechTupleEquiv _ k _
  rw [coverCechTupleEquiv_map]
  apply congrArg (coverCechTupleEquiv _ k)
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  apply Subtype.ext
  apply (X.toSSetObjEquiv (op ⦋n⦌)).injective
  ext t
  rfl

/-- The nerve's common simplex is precisely the image of the
intersection simplex under inclusion into any indicated cover member. -/
theorem smallSingularCechSimplexEquiv_base_local (n k : ℕ)
    (a : Fin (k + 1) → ι)
    (σ : Basic.singularSimplices (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n)
    (j : Fin (k + 1)) :
    WidePullback.base (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection
      (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n))
        (smallSingularCechSimplexEquiv X U n k ⟨a, σ⟩) =
      (SmallCochainCech.localSmallSingularMap X (fun i => (U i : Set X)) (a j)).app (op ⦋n⦌)
        ((TopCat.toSSet.map ((Opens.toTopCat X).map
          (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le U a j)))).app (op ⦋n⦌) σ) := by
  calc
    _ = (intersectionSmallSingularSimplexEquiv X U n a σ).1 :=
      coverCechTupleToNerve_base _ k ⟨a, intersectionSmallSingularSimplexEquiv X U n a σ⟩
    _ = _ := by
      apply Subtype.ext
      apply (X.toSSetObjEquiv (op ⦋n⦌)).injective
      ext t
      rfl

variable (M : ModuleCat.{0} ℂ)

/-- The actual row cochain object is the product of singular cochain
modules on the corresponding finite open intersections. -/
def smallSingularCechDegreeEquiv (n k : ℕ) :
    (SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).X k ≃ₗ[ℂ]
      DeRham.Comparison.SmoothCech.CechCochain (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U k :=
  ((SmallCochainCech.smallSingularCechDegreewiseFunctionIso X (fun i => (U i : Set X)) M n k).toLinearEquiv.trans
    (LinearEquiv.piCongrLeft' ℂ (fun _ => M)
      (smallSingularCechSimplexEquiv X U n k).symm)).trans
    ((LinearEquiv.piCurry ℂ (fun (a : Fin (k + 1) → ι)
      (_ : Basic.singularSimplices (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n) => M)).trans
        (LinearEquiv.piCongrRight (fun a =>
          (Coefficients.singularDegreewiseFunctionIso M
            (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv.symm)))

/-- Evaluation of the cochain identification at an intersection simplex
is evaluation on its corresponding actual nerve simplex. -/
theorem smallSingularCechDegreeEquiv_evaluation (n k : ℕ)
    (c : (SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).X k)
    (a : Fin (k + 1) → ι)
    (σ : Basic.singularSimplices (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n) :
    (Coefficients.singularDegreewiseFunctionIso M (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).hom
        (smallSingularCechDegreeEquiv X U M n k c a) σ =
      (SmallCochainCech.smallSingularCechDegreewiseFunctionIso X (fun i => (U i : Set X)) M n k).hom c
        (smallSingularCechSimplexEquiv X U n k ⟨a, σ⟩) := by
  change ((Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv
      ((Coefficients.singularDegreewiseFunctionIso M
        (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv.symm
          (fun τ => (SmallCochainCech.smallSingularCechDegreewiseFunctionIso X
            (fun i => (U i : Set X)) M n k).hom c
              (smallSingularCechSimplexEquiv X U n k ⟨a, τ⟩)))) σ = _
  rw [LinearEquiv.apply_symm_apply]

/-- The degreewise identification preserves the existing signed Čech
differential, with its actual presheaf restriction maps. -/
theorem smallSingularCechDegreeEquiv_d (n k : ℕ)
    (c : (SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).X k) :
    smallSingularCechDegreeEquiv X U M n (k + 1)
        ((SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).d k (k + 1) c) =
      DeRham.Comparison.SmoothCech.cechDelta (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U k
        (smallSingularCechDegreeEquiv X U M n k c) := by
  funext a
  apply (Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv.injective
  funext σ
  change (Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).hom _ σ =
      (Coefficients.singularDegreewiseFunctionIso M
        (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).hom _ σ
  rw [smallSingularCechDegreeEquiv_evaluation, SmallCochainCech.smallSingularCechCochains_d_apply,
    DeRham.Comparison.SmoothCech.cechDelta_apply]
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun v : M => ((-1 : ℤ) ^ j.val) • v)
  change (SmallCochainCech.smallSingularCechDegreewiseFunctionIso X (fun i => (U i : Set X)) M n k).hom c
      ((DeRham.Comparison.CechCoverRows.coverCechNerve (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X
        (fun i => (U i : Set X)) n)).left.map (SimplexCategory.δ j).op
          (smallSingularCechSimplexEquiv X U n (k + 1) ⟨a, σ⟩)) =
    (Coefficients.degreewiseFunctionIso (TopCat.toSSet.obj
      (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a))) M n).hom
        ((Functor.simplicialPullback M (TopCat.toSSet.map ((Opens.toTopCat X).map
          (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove))))).f n
            (smallSingularCechDegreeEquiv X U M n k c (a ∘ j.succAbove))) σ
  rw [smallSingularCechSimplexEquiv_map]
  let g : TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶
      TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U (a ∘ j.succAbove)) :=
    (Opens.toTopCat X).map (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove))
  exact (smallSingularCechDegreeEquiv_evaluation X U M n k c (a ∘ j.succAbove)
    ((TopCat.toSSet.map g).app (op ⦋n⦌) σ)).symm.trans
      (Formulas.degreewiseFunctionIso_pullback M (TopCat.toSSet.map g)
        (smallSingularCechDegreeEquiv X U M n k c (a ∘ j.succAbove)) σ).symm

/-- Canonical isomorphism from the already checked small-singular Čech
row to the existing product-over-intersections Čech presheaf complex. -/
def smallSingularCechComparisonIso (n : ℕ) :
    SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n ≅
      DeRham.Comparison.SmoothCech.cechComplex (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k => (smallSingularCechDegreeEquiv X U M n k).toModuleIso) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ConcreteCategory.ext_apply
      intro c
      rw [DeRham.Comparison.SmoothCech.cechComplex_d]
      exact (smallSingularCechDegreeEquiv_d X U M n i c).symm)

@[simp]
theorem smallSingularCechComparisonIso_hom_f (n k : ℕ) :
    (smallSingularCechComparisonIso X U M n).hom.f k =
      ModuleCat.ofHom (smallSingularCechDegreeEquiv X U M n k).toLinearMap := rfl

/-- Positive-degree Čech exactness in the standard presheaf presentation,
transferred through the proved complex isomorphism. -/
theorem singularCochainCech_exactAt_succ (n k : ℕ) :
    (DeRham.Comparison.SmoothCech.cechComplex (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U).ExactAt
      (k + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (SmallCochainCech.smallSingularCechCochains_exactAt_succ X (fun i => (U i : Set X)) M n k).isZero_homology.of_iso
      (((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (.up ℕ) (k + 1)).mapIso
        (smallSingularCechComparisonIso X U M n)).symm)

/-- Zeroth cohomology of the standard Čech row is the actual small
singular cochain module in the fixed singular degree. -/
def singularCochainCechHomologyZeroIso (n : ℕ) :
    (DeRham.Comparison.SmoothCech.cechComplex (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U).homology 0 ≅
      (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (.up ℕ) 0).mapIso
    (smallSingularCechComparisonIso X U M n)).symm ≪≫
      SmallCochainCech.smallSingularCechCochainsHomologyZeroIso X (fun i => (U i : Set X)) M n

/-- Augmentation from actual small singular cochains to the actual
nerve row, using its common-simplex projection. -/
def smallSingularCechNerveAugmentation (n : ℕ) :
    (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n →ₗ[ℂ]
      (SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).X 0 :=
  (coverCechCochainAugmentation
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M).hom.comp
      (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X (fun i => (U i : Set X)) n).hom.hom

theorem smallSingularCechNerveAugmentation_evaluation (n : ℕ)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n)
    (z : (DeRham.Comparison.CechCoverRows.coverCechNerve (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X
      (fun i => (U i : Set X)) n)).left _⦋0⦌) :
    (SmallCochainCech.smallSingularCechDegreewiseFunctionIso X (fun i => (U i : Set X)) M n 0).hom
        (smallSingularCechNerveAugmentation X U M n c) z =
      (DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X (fun i => (U i : Set X)) n).hom c
        (WidePullback.base (fun _ : Fin 1 => DeRham.Comparison.CechCoverRows.coverProjection
          (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n)) z) :=
  coverCechCochainAugmentation_evaluation _ M _ z

/-- Augmentation in the existing intersection presentation is the
actual singular restriction to each singleton intersection. -/
def smallSingularCechStandardAugmentation (n : ℕ) :
    (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n →ₗ[ℂ]
      DeRham.Comparison.SmoothCech.CechCochain (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0 where
  toFun c a :=
    (Functor.singularPullback M ((Opens.toTopCat X).map
      (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le U a 0)))).f n
        ((SmallCochainCech.smallSingularLocalRestriction X (fun i => (U i : Set X)) M (a 0)).f n c)
  map_add' c d := by
    funext a
    simp only [map_add, Pi.add_apply]
  map_smul' a c := by
    funext b
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The canonical complex isomorphism preserves the actual restriction
augmentation, not merely an unspecified isomorphism on cohomology. -/
theorem smallSingularCechComparisonIso_augmentation (n : ℕ)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    (smallSingularCechComparisonIso X U M n).hom.f 0
        (smallSingularCechNerveAugmentation X U M n c) =
      smallSingularCechStandardAugmentation X U M n c := by
  funext a
  apply (Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).toLinearEquiv.injective
  funext σ
  change (Coefficients.singularDegreewiseFunctionIso M
    (TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a)) n).hom
      (smallSingularCechDegreeEquiv X U M n 0
        (smallSingularCechNerveAugmentation X U M n c) a) σ = _
  rw [smallSingularCechDegreeEquiv_evaluation, smallSingularCechNerveAugmentation_evaluation,
    smallSingularCechSimplexEquiv_base_local X U n 0 a σ 0]
  let g : TopCat.of (DeRham.Comparison.SmoothCech.cechIntersection U a) ⟶ TopCat.of (U (a 0)) :=
    (Opens.toTopCat X).map (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le U a 0))
  exact (Formulas.degreewiseFunctionIso_pullback M
    (SmallCochainCech.localSmallSingularMap X (fun i => (U i : Set X)) (a 0)) c
      ((TopCat.toSSet.map g).app (op ⦋n⦌) σ)).symm.trans
        (Formulas.degreewiseFunctionIso_pullback M (TopCat.toSSet.map g)
          ((SmallCochainCech.smallSingularLocalRestriction X (fun i => (U i : Set X)) M (a 0)).f n c) σ).symm

/-- The actual standard augmentation lands in the kernel of the
existing degree-zero Čech differential. -/
theorem smallSingularCechStandardAugmentation_delta (n : ℕ)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    DeRham.Comparison.SmoothCech.cechDelta (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U 0
      (smallSingularCechStandardAugmentation X U M n c) = 0 := by
  have h := smallSingularCechDegreeEquiv_d X U M n 0
    (smallSingularCechNerveAugmentation X U M n c)
  have ha : smallSingularCechDegreeEquiv X U M n 0
      (smallSingularCechNerveAugmentation X U M n c) =
        smallSingularCechStandardAugmentation X U M n c :=
    smallSingularCechComparisonIso_augmentation X U M n c
  rw [ha] at h
  have hz : (SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).d 0 1
      (smallSingularCechNerveAugmentation X U M n c) = 0 :=
    coverCechCochainAugmentation_d_zero _ M _
  rw [hz, map_zero] at h
  exact h.symm

/-- The nerve-row augmentation is a zero Čech cocycle on every small
singular cochain. -/
theorem smallSingularCechNerveAugmentation_d_zero (n : ℕ)
    (c : (DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) :
    (SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n).d 0 1
      (smallSingularCechNerveAugmentation X U M n c) = 0 :=
  coverCechCochainAugmentation_d_zero
    (DeRham.Comparison.CechCoverRows.smallSingularSimplexCover X (fun i => (U i : Set X)) n) M
    ((DeRham.Comparison.SmallSingularCochains.smallSingularDegreewiseFunctionIso M X (fun i => (U i : Set X)) n).hom c)

/-- The actual augmented nerve row, bundled as a cochain map from the
small singular cochain module concentrated in Čech degree zero. -/
def smallSingularCechNerveAugmentationMap (n : ℕ) :
    (CochainComplex.single₀ (ModuleCat.{0} ℂ)).obj
        ((DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) ⟶
      SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n :=
  (CochainComplex.fromSingle₀Equiv
    (SmallCochainCech.smallSingularCechCochains X (fun i => (U i : Set X)) M n)
    ((DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n)).symm
    ⟨ModuleCat.ofHom (smallSingularCechNerveAugmentation X U M n), by
      apply ConcreteCategory.ext_apply
      intro c
      exact smallSingularCechNerveAugmentation_d_zero X U M n c⟩

/-- The standard intersection Čech row with its actual singular
restriction augmentation, bundled as a cochain map. -/
def smallSingularCechStandardAugmentationMap (n : ℕ) :
    (CochainComplex.single₀ (ModuleCat.{0} ℂ)).obj
        ((DeRham.Comparison.SmallSingularCochains.smallSingularCochains M X (fun i => (U i : Set X))).X n) ⟶
      DeRham.Comparison.SmoothCech.cechComplex (DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf M X n) U :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (smallSingularCechStandardAugmentation X U M n), by
      apply ConcreteCategory.ext_apply
      intro c
      rw [DeRham.Comparison.SmoothCech.cechComplex_d]
      exact smallSingularCechStandardAugmentation_delta X U M n c⟩

/-- The augmentation square commutes as an equality of genuine cochain
maps between the two already identified Čech row presentations. -/
theorem smallSingularCechComparisonIso_augmentationMap (n : ℕ) :
    smallSingularCechNerveAugmentationMap X U M n ≫
        (smallSingularCechComparisonIso X U M n).hom =
      smallSingularCechStandardAugmentationMap X U M n := by
  apply HomologicalComplex.from_single_hom_ext
  change ((smallSingularCechNerveAugmentationMap X U M n).f 0) ≫
    ((smallSingularCechComparisonIso X U M n).hom.f 0) =
      (smallSingularCechStandardAugmentationMap X U M n).f 0
  rw [smallSingularCechNerveAugmentationMap, smallSingularCechStandardAugmentationMap,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  apply ConcreteCategory.ext_apply
  intro c
  exact smallSingularCechComparisonIso_augmentation X U M n c

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechComparison
