import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothOpenReflection
import OAI.AlgebraicTopology.Cohomology.Singular.SmallCochainCechExact

/-! # Manifold Smooth Small Cech -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallCech

noncomputable section

/-!
# Čech rows for actual cover-small manifold-smooth cochains

The cover of actual small smooth simplices by image containment has the
already constructed split Čech nerve. Open-target reflection identifies its
local factors with the actual manifold-smooth simplices on the corresponding
open intersections. The resulting cochain isomorphism preserves the existing
Čech differential and the canonical restriction augmentation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial BigOperators _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type}

section ImageCover

variable (V : ι → Set X)

/-- Image containment gives a cover of the actual small smooth simplices. -/
def manifoldSmoothSmallSimplexCover (n : ℕ) (i : ι) :
    Set (ManifoldSmoothSmall.ManifoldSmoothSmallSimplex E X V n) :=
  {σ | Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ.val) ⊆ V i}

/-- Coverage follows from the actual smallness condition, with no spatial
cover assumption. -/
theorem manifoldSmoothSmallSimplexCover_covers (n : ℕ)
    (σ : ManifoldSmoothSmall.ManifoldSmoothSmallSimplex E X V n) :
    ∃ i, σ ∈ manifoldSmoothSmallSimplexCover E X V n i := σ.property.1

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)

/-- The split Čech row for the genuine cover of small smooth simplices. -/
abbrev manifoldSmoothSmallCechCochains (n : ℕ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  SmallCochainCech.coverCechCochains A (manifoldSmoothSmallSimplexCover E X V n)

/-- Function coordinates on the actual nerve, inherited from simplicial
cochains. -/
def manifoldSmoothSmallCechDegreewiseFunctionIso (n k : ℕ) :
    (manifoldSmoothSmallCechCochains E X V A n).X k ≅
      ModuleCat.of R ((DeRham.Comparison.CechCoverRows.coverCechNerve
        (manifoldSmoothSmallSimplexCover E X V n)).left _⦋k⦌ → A) :=
  Coefficients.degreewiseFunctionIso _ A k

/-- The actual row differential is the alternating face sum. -/
theorem manifoldSmoothSmallCechCochains_d_apply (n k : ℕ)
    (c : (manifoldSmoothSmallCechCochains E X V A n).X k)
    (σ : (DeRham.Comparison.CechCoverRows.coverCechNerve
      (manifoldSmoothSmallSimplexCover E X V n)).left _⦋k + 1⦌) :
    (manifoldSmoothSmallCechDegreewiseFunctionIso E X V A n (k + 1)).hom
        ((manifoldSmoothSmallCechCochains E X V A n).d k (k + 1) c) σ =
      ∑ j : Fin (k + 2), ((-1 : ℤ) ^ j.val) •
        (manifoldSmoothSmallCechDegreewiseFunctionIso E X V A n k).hom c
          ((DeRham.Comparison.CechCoverRows.coverCechNerve
            (manifoldSmoothSmallSimplexCover E X V n)).left.δ j σ) :=
  Formulas.degreewiseFunctionIso_coboundary _ A c σ

/-- Positive Čech exactness follows from the proved split-nerve contraction. -/
theorem manifoldSmoothSmallCechCochains_exactAt_succ (n k : ℕ) :
    (manifoldSmoothSmallCechCochains E X V A n).ExactAt (k + 1) :=
  SmallCochainCech.coverCechCochains_exactAt_succ A (manifoldSmoothSmallSimplexCover E X V n)
    (manifoldSmoothSmallSimplexCover_covers E X V n) k

/-- Zeroth row cohomology is the actual small smooth cochain module. -/
def manifoldSmoothSmallCechCochainsHomologyZeroIso (n : ℕ) :
    (manifoldSmoothSmallCechCochains E X V A n).homology 0 ≅
      (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X V).X n :=
  SmallCochainCech.coverCechCochainsHomologyZeroIso A (manifoldSmoothSmallSimplexCover E X V n)
    (manifoldSmoothSmallSimplexCover_covers E X V n) ≪≫
      (ManifoldSmoothSmall.manifoldSmoothSmallDegreewiseFunctionIso E A X V n).symm

end ImageCover

section OpenFactors

/-- Open-target reflection gives the exact local factor identification:
smooth simplices in an open set are ambient smooth simplices lying in it. -/
def manifoldSmoothSimplexSubtypeEquiv (W : Opens X) (n : ℕ) :
    ManifoldSmoothOpenReflection.manifoldSmoothSimplices E W n ≃
      {σ : ManifoldSmoothOpenReflection.manifoldSmoothSimplices E X n //
        Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ.val) ⊆ W} where
  toFun σ := ⟨(ManifoldSmoothOpenReflection.manifoldSmoothOpenInclusion E W).app (op ⦋n⦌) σ, by
    rintro _ ⟨t, rfl⟩
    exact (((TopCat.of W).toSSetObjEquiv (op ⦋n⦌) σ.val) t).property⟩
  invFun σ := ManifoldSmoothOpenReflection.manifoldSmoothSimplexLift E W σ.1 σ.2
  left_inv σ := by
    apply ManifoldSmoothOpenReflection.manifoldSmoothOpenInclusion_injective E W n
    exact ManifoldSmoothOpenReflection.manifoldSmoothSimplexLift_spec E W _ _
  right_inv σ := by
    apply Subtype.ext
    exact ManifoldSmoothOpenReflection.manifoldSmoothSimplexLift_spec E W _ _

variable (U : ι → Opens X)

/-- Smooth simplices on a finite open intersection are exactly the small
smooth simplices lying in every member of the tuple. -/
def intersectionManifoldSmoothSmallSimplexEquiv (n : ℕ) {k : ℕ}
    (a : Fin (k + 1) → ι) :
    ManifoldSmoothOpenReflection.manifoldSmoothSimplices E (DeRham.Comparison.SmoothCech.cechIntersection U a) n ≃
      {σ : ManifoldSmoothSmall.ManifoldSmoothSmallSimplex E X (fun i => (U i : Set X)) n //
        ∀ j, σ ∈ manifoldSmoothSmallSimplexCover E X
          (fun i => (U i : Set X)) n (a j)} :=
  (manifoldSmoothSimplexSubtypeEquiv E X (DeRham.Comparison.SmoothCech.cechIntersection U a) n).trans
    { toFun := fun σ =>
        ⟨⟨σ.1.val, ⟨⟨a 0, fun _y hy => DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 (σ.2 hy)⟩,
          σ.1.property⟩⟩,
          fun j _y hy => DeRham.Comparison.SmoothCech.cechIntersection_le U a j (σ.2 hy)⟩
      invFun := fun σ =>
        ⟨⟨σ.1.val, σ.1.property.2⟩, fun y hy => (DeRham.Comparison.SmoothCech.mem_cechIntersection U a y).2
          (fun j => σ.2 j hy)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The actual nerve is the disjoint union of smooth simplices on the
corresponding finite open intersections. -/
def manifoldSmoothSmallCechSimplexEquiv (n k : ℕ) :
    (Σ a : Fin (k + 1) → ι,
      ManifoldSmoothOpenReflection.manifoldSmoothSimplices E (DeRham.Comparison.SmoothCech.cechIntersection U a) n) ≃
        (DeRham.Comparison.CechCoverRows.coverCechNerve (manifoldSmoothSmallSimplexCover E X
          (fun i => (U i : Set X)) n)).left _⦋k⦌ :=
  (Equiv.sigmaCongrRight (fun a =>
    intersectionManifoldSmoothSmallSimplexEquiv E X U n a)).trans
      (SmallCochainCechComparison.coverCechTupleEquiv (manifoldSmoothSmallSimplexCover E X
        (fun i => (U i : Set X)) n) k)

/-- The factor identification preserves every Čech simplicial operator. -/
theorem manifoldSmoothSmallCechSimplexEquiv_map (n : ℕ) {k l : ℕ}
    (f : ⦋k⦌ ⟶ ⦋l⦌) (a : Fin (l + 1) → ι)
    (σ : ManifoldSmoothOpenReflection.manifoldSmoothSimplices E (DeRham.Comparison.SmoothCech.cechIntersection U a) n) :
    (DeRham.Comparison.CechCoverRows.coverCechNerve (manifoldSmoothSmallSimplexCover E X
      (fun i => (U i : Set X)) n)).left.map f.op
        (manifoldSmoothSmallCechSimplexEquiv E X U n l ⟨a, σ⟩) =
      manifoldSmoothSmallCechSimplexEquiv E X U n k
        ⟨a ∘ f.toOrderHom,
          ((ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E X).map
            (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a f.toOrderHom))).app
              (op ⦋n⦌) σ⟩ := by
  change (DeRham.Comparison.CechCoverRows.coverCechNerve _).left.map f.op
      (SmallCochainCechComparison.coverCechTupleEquiv _ l
        ⟨a, intersectionManifoldSmoothSmallSimplexEquiv E X U n a σ⟩) =
    SmallCochainCechComparison.coverCechTupleEquiv _ k _
  rw [SmallCochainCechComparison.coverCechTupleEquiv_map]
  apply congrArg (SmallCochainCechComparison.coverCechTupleEquiv _ k)
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply Subtype.ext
  apply Subtype.ext
  apply ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)).injective
  ext t
  rfl

/-- The nerve's common small smooth simplex is its actual local image. -/
theorem manifoldSmoothSmallCechSimplexEquiv_base_local (n k : ℕ)
    (a : Fin (k + 1) → ι)
    (σ : ManifoldSmoothOpenReflection.manifoldSmoothSimplices E (DeRham.Comparison.SmoothCech.cechIntersection U a) n)
    (j : Fin (k + 1)) :
    WidePullback.base (fun _ : Fin (k + 1) => DeRham.Comparison.CechCoverRows.coverProjection
      (manifoldSmoothSmallSimplexCover E X (fun i => (U i : Set X)) n))
        (manifoldSmoothSmallCechSimplexEquiv E X U n k ⟨a, σ⟩) =
      (ManifoldSmoothSmall.manifoldSmoothSmallLocalMap E X U (a j)).app (op ⦋n⦌)
        (((ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E X).map
          (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le U a j))).app (op ⦋n⦌) σ) := by
  calc
    _ = (intersectionManifoldSmoothSmallSimplexEquiv E X U n a σ).1 :=
      SmallCochainCechComparison.coverCechTupleToNerve_base _ k
        ⟨a, intersectionManifoldSmoothSmallSimplexEquiv E X U n a σ⟩
    _ = _ := by
      apply Subtype.ext
      apply ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)).injective
      ext t
      rfl

end OpenFactors

variable (U : ι → Opens X) (A : ModuleCat.{0} ℂ)

/-- The actual row cochains are the existing product of smooth cochain
modules on finite open intersections. -/
def manifoldSmoothSmallCechDegreeEquiv (n k : ℕ) :
    (manifoldSmoothSmallCechCochains E X (fun i => (U i : Set X)) A n).X k ≃ₗ[ℂ]
      DeRham.Comparison.SmoothCech.CechCochain (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U k :=
  ((manifoldSmoothSmallCechDegreewiseFunctionIso E X
    (fun i => (U i : Set X)) A n k).toLinearEquiv.trans
      (LinearEquiv.piCongrLeft' ℂ (fun _ => A)
        (manifoldSmoothSmallCechSimplexEquiv E X U n k).symm)).trans
    ((LinearEquiv.piCurry ℂ (fun (a : Fin (k + 1) → ι)
      (_ : ManifoldSmoothOpenReflection.manifoldSmoothSimplices E (DeRham.Comparison.SmoothCech.cechIntersection U a) n) => A)).trans
        (LinearEquiv.piCongrRight (fun a =>
          (Coefficients.degreewiseFunctionIso
            (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet
              A n).toLinearEquiv.symm)))

/-- The comparison evaluates on the same actual local smooth simplex. -/
theorem manifoldSmoothSmallCechDegreeEquiv_evaluation (n k : ℕ)
    (c : (manifoldSmoothSmallCechCochains E X (fun i => (U i : Set X)) A n).X k)
    (a : Fin (k + 1) → ι)
    (σ : ManifoldSmoothOpenReflection.manifoldSmoothSimplices E (DeRham.Comparison.SmoothCech.cechIntersection U a) n) :
    (Coefficients.degreewiseFunctionIso
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet A n).hom
        (manifoldSmoothSmallCechDegreeEquiv E X U A n k c a) σ =
      (manifoldSmoothSmallCechDegreewiseFunctionIso E X
        (fun i => (U i : Set X)) A n k).hom c
          (manifoldSmoothSmallCechSimplexEquiv E X U n k ⟨a, σ⟩) := by
  change ((Coefficients.degreewiseFunctionIso
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet
      A n).toLinearEquiv
        ((Coefficients.degreewiseFunctionIso
          (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet
            A n).toLinearEquiv.symm
          (fun τ => (manifoldSmoothSmallCechDegreewiseFunctionIso E X
            (fun i => (U i : Set X)) A n k).hom c
              (manifoldSmoothSmallCechSimplexEquiv E X U n k ⟨a, τ⟩)))) σ = _
  rw [LinearEquiv.apply_symm_apply]

/-- The identification preserves the existing signed Čech differential
and its actual smooth restriction maps. -/
theorem manifoldSmoothSmallCechDegreeEquiv_d (n k : ℕ)
    (c : (manifoldSmoothSmallCechCochains E X (fun i => (U i : Set X)) A n).X k) :
    manifoldSmoothSmallCechDegreeEquiv E X U A n (k + 1)
        ((manifoldSmoothSmallCechCochains E X (fun i => (U i : Set X)) A n).d k (k + 1) c) =
      DeRham.Comparison.SmoothCech.cechDelta (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U k
        (manifoldSmoothSmallCechDegreeEquiv E X U A n k c) := by
  funext a
  apply (Coefficients.degreewiseFunctionIso
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet
      A n).toLinearEquiv.injective
  funext σ
  change (Coefficients.degreewiseFunctionIso
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet
      A n).hom _ σ =
    (Coefficients.degreewiseFunctionIso
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet
        A n).hom _ σ
  rw [manifoldSmoothSmallCechDegreeEquiv_evaluation, manifoldSmoothSmallCechCochains_d_apply,
    DeRham.Comparison.SmoothCech.cechDelta_apply]
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun v : A => ((-1 : ℤ) ^ j.val) • v)
  change (manifoldSmoothSmallCechDegreewiseFunctionIso E X
    (fun i => (U i : Set X)) A n k).hom c
      ((DeRham.Comparison.CechCoverRows.coverCechNerve (manifoldSmoothSmallSimplexCover E X
        (fun i => (U i : Set X)) n)).left.map (SimplexCategory.δ j).op
          (manifoldSmoothSmallCechSimplexEquiv E X U n (k + 1) ⟨a, σ⟩)) =
    (Coefficients.degreewiseFunctionIso
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet A n).hom
        ((Functor.simplicialPullback A ((ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E X).map
          (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove)))).f n
            (manifoldSmoothSmallCechDegreeEquiv E X U A n k c (a ∘ j.succAbove))) σ
  rw [manifoldSmoothSmallCechSimplexEquiv_map]
  let g := (ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E X).map
    (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le_precomp U a j.succAbove))
  exact (manifoldSmoothSmallCechDegreeEquiv_evaluation E X U A n k c (a ∘ j.succAbove)
    (g.app (op ⦋n⦌) σ)).symm.trans
      (Formulas.degreewiseFunctionIso_pullback A g
        (manifoldSmoothSmallCechDegreeEquiv E X U A n k c (a ∘ j.succAbove)) σ).symm

/-- Isomorphism to the existing smooth-cochain presheaf Čech complex. -/
def manifoldSmoothSmallCechComparisonIso (n : ℕ) :
    manifoldSmoothSmallCechCochains E X (fun i => (U i : Set X)) A n ≅
      DeRham.Comparison.SmoothCech.cechComplex (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k => (manifoldSmoothSmallCechDegreeEquiv E X U A n k).toModuleIso) (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ConcreteCategory.ext_apply
      intro c
      rw [DeRham.Comparison.SmoothCech.cechComplex_d]
      exact (manifoldSmoothSmallCechDegreeEquiv_d E X U A n i c).symm)

@[simp]
theorem manifoldSmoothSmallCechComparisonIso_hom_f (n k : ℕ) :
    (manifoldSmoothSmallCechComparisonIso E X U A n).hom.f k =
      ModuleCat.ofHom (manifoldSmoothSmallCechDegreeEquiv E X U A n k).toLinearMap := rfl

/-- Positive exactness for the actual smooth presheaf Čech row. -/
theorem manifoldSmoothCochainCech_exactAt_succ (n k : ℕ) :
    (DeRham.Comparison.SmoothCech.cechComplex (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U).ExactAt
      (k + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (manifoldSmoothSmallCechCochains_exactAt_succ E X
    (fun i => (U i : Set X)) A n k).isZero_homology.of_iso
      (((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (.up ℕ) (k + 1)).mapIso
        (manifoldSmoothSmallCechComparisonIso E X U A n)).symm)

/-- Zeroth cohomology of the standard row is the genuine small smooth
cochain module. -/
def manifoldSmoothCochainCechHomologyZeroIso (n : ℕ) :
    (DeRham.Comparison.SmoothCech.cechComplex (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U).homology 0 ≅
      (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (.up ℕ) 0).mapIso
    (manifoldSmoothSmallCechComparisonIso E X U A n)).symm ≪≫
      manifoldSmoothSmallCechCochainsHomologyZeroIso E X
        (fun i => (U i : Set X)) A n

/-- Actual small smooth cochains augment the nerve row through its
common-simplex projection. -/
def manifoldSmoothSmallCechNerveAugmentation (n : ℕ) :
    (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n →ₗ[ℂ]
      (manifoldSmoothSmallCechCochains E X (fun i => (U i : Set X)) A n).X 0 :=
  (SmallCochainCechComparison.coverCechCochainAugmentation
    (manifoldSmoothSmallSimplexCover E X (fun i => (U i : Set X)) n) A).hom.comp
      (ManifoldSmoothSmall.manifoldSmoothSmallDegreewiseFunctionIso E A X (fun i => (U i : Set X)) n).hom.hom

theorem manifoldSmoothSmallCechNerveAugmentation_evaluation (n : ℕ)
    (c : (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n)
    (z : (DeRham.Comparison.CechCoverRows.coverCechNerve (manifoldSmoothSmallSimplexCover E X
      (fun i => (U i : Set X)) n)).left _⦋0⦌) :
    (manifoldSmoothSmallCechDegreewiseFunctionIso E X
      (fun i => (U i : Set X)) A n 0).hom
        (manifoldSmoothSmallCechNerveAugmentation E X U A n c) z =
      (ManifoldSmoothSmall.manifoldSmoothSmallDegreewiseFunctionIso E A X (fun i => (U i : Set X)) n).hom c
        (WidePullback.base (fun _ : Fin 1 => DeRham.Comparison.CechCoverRows.coverProjection
          (manifoldSmoothSmallSimplexCover E X (fun i => (U i : Set X)) n)) z) :=
  SmallCochainCechComparison.coverCechCochainAugmentation_evaluation _ A _ z

/-- The standard augmentation uses the existing actual small smooth local
restriction, followed by restriction to the singleton intersection. -/
def manifoldSmoothSmallCechStandardAugmentation (n : ℕ) :
    (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n →ₗ[ℂ]
      DeRham.Comparison.SmoothCech.CechCochain (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U 0 where
  toFun c a :=
    (ManifoldSmoothPresheaf.manifoldSmoothOpenRestriction E X A
      (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le U a 0))).f n
        ((ManifoldSmoothSmall.manifoldSmoothSmallLocalRestriction E A X U (a 0)).f n c)
  map_add' c d := by
    funext a
    simp only [map_add, Pi.add_apply]
  map_smul' a c := by
    funext b
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The row isomorphism preserves the canonical restriction augmentation. -/
theorem manifoldSmoothSmallCechComparisonIso_augmentation (n : ℕ)
    (c : (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n) :
    (manifoldSmoothSmallCechComparisonIso E X U A n).hom.f 0
        (manifoldSmoothSmallCechNerveAugmentation E X U A n c) =
      manifoldSmoothSmallCechStandardAugmentation E X U A n c := by
  funext a
  apply (Coefficients.degreewiseFunctionIso
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet
      A n).toLinearEquiv.injective
  funext σ
  change (Coefficients.degreewiseFunctionIso
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (DeRham.Comparison.SmoothCech.cechIntersection U a)).toSSet A n).hom
      (manifoldSmoothSmallCechDegreeEquiv E X U A n 0
        (manifoldSmoothSmallCechNerveAugmentation E X U A n c) a) σ = _
  rw [manifoldSmoothSmallCechDegreeEquiv_evaluation,
    manifoldSmoothSmallCechNerveAugmentation_evaluation,
    manifoldSmoothSmallCechSimplexEquiv_base_local E X U n 0 a σ 0]
  let g := (ManifoldSmoothPresheaf.manifoldOpenSmoothSingularFunctor E X).map
    (homOfLE (DeRham.Comparison.SmoothCech.cechIntersection_le U a 0))
  exact (Formulas.degreewiseFunctionIso_pullback A (ManifoldSmoothSmall.manifoldSmoothSmallLocalMap E X U (a 0)) c
    (g.app (op ⦋n⦌) σ)).symm.trans
      (Formulas.degreewiseFunctionIso_pullback A g
        ((ManifoldSmoothSmall.manifoldSmoothSmallLocalRestriction E A X U (a 0)).f n c) σ).symm

/-- The standard augmentation lands in the kernel of the actual Čech
differential. -/
theorem manifoldSmoothSmallCechStandardAugmentation_delta (n : ℕ)
    (c : (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n) :
    DeRham.Comparison.SmoothCech.cechDelta (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U 0
      (manifoldSmoothSmallCechStandardAugmentation E X U A n c) = 0 := by
  have h := manifoldSmoothSmallCechDegreeEquiv_d E X U A n 0
    (manifoldSmoothSmallCechNerveAugmentation E X U A n c)
  have ha : manifoldSmoothSmallCechDegreeEquiv E X U A n 0
      (manifoldSmoothSmallCechNerveAugmentation E X U A n c) =
        manifoldSmoothSmallCechStandardAugmentation E X U A n c :=
    manifoldSmoothSmallCechComparisonIso_augmentation E X U A n c
  rw [ha] at h
  have hz : (manifoldSmoothSmallCechCochains E X (fun i => (U i : Set X)) A n).d 0 1
      (manifoldSmoothSmallCechNerveAugmentation E X U A n c) = 0 :=
    SmallCochainCechComparison.coverCechCochainAugmentation_d_zero _ A _
  rw [hz, map_zero] at h
  exact h.symm

/-- The canonical smooth-small augmentation is injective. -/
theorem manifoldSmoothSmallCechStandardAugmentation_injective (n : ℕ) :
    Function.Injective (manifoldSmoothSmallCechStandardAugmentation E X U A n) := by
  intro c d h
  apply (ManifoldSmoothSmall.manifoldSmoothSmallDegreewiseFunctionIso E A X
    (fun i => (U i : Set X)) n).toLinearEquiv.injective
  apply SmallCochainCechExact.coverCechCochainAugmentation_injective
    (manifoldSmoothSmallSimplexCover E X (fun i => (U i : Set X)) n) A
    (manifoldSmoothSmallSimplexCover_covers E X (fun i => (U i : Set X)) n)
  apply (manifoldSmoothSmallCechDegreeEquiv E X U A n 0).injective
  exact (manifoldSmoothSmallCechComparisonIso_augmentation E X U A n c).trans
    (h.trans (manifoldSmoothSmallCechComparisonIso_augmentation E X U A n d).symm)

/-- Every standard smooth-cochain zero Čech cocycle is the actual
restriction of a small smooth cochain. -/
theorem manifoldSmoothSmallCechStandardAugmentation_preimage (n : ℕ)
    (c : DeRham.Comparison.SmoothCech.CechCochain (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U 0)
    (hc : DeRham.Comparison.SmoothCech.cechDelta (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U 0 c = 0) :
    ∃ b : (ManifoldSmoothSmall.manifoldSmoothSmallCochains E A X (fun i => (U i : Set X))).X n,
      manifoldSmoothSmallCechStandardAugmentation E X U A n b = c := by
  let bN := (manifoldSmoothSmallCechDegreeEquiv E X U A n 0).symm c
  have hbN : (manifoldSmoothSmallCechCochains E X
      (fun i => (U i : Set X)) A n).d 0 1 bN = 0 := by
    apply (manifoldSmoothSmallCechDegreeEquiv E X U A n 1).injective
    calc
      _ = DeRham.Comparison.SmoothCech.cechDelta (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U 0
          (manifoldSmoothSmallCechDegreeEquiv E X U A n 0 bN) :=
        manifoldSmoothSmallCechDegreeEquiv_d E X U A n 0 bN
      _ = 0 := by
        change DeRham.Comparison.SmoothCech.cechDelta (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U 0
          ((manifoldSmoothSmallCechDegreeEquiv E X U A n 0)
            ((manifoldSmoothSmallCechDegreeEquiv E X U A n 0).symm c)) = 0
        rw [LinearEquiv.apply_symm_apply]
        exact hc
      _ = _ := (map_zero (manifoldSmoothSmallCechDegreeEquiv E X U A n 1)).symm
  obtain ⟨f, hf⟩ := SmallCochainCechExact.coverCechCochainAugmentation_preimage
    (manifoldSmoothSmallSimplexCover E X (fun i => (U i : Set X)) n) A
    (manifoldSmoothSmallSimplexCover_covers E X (fun i => (U i : Set X)) n) bN hbN
  let b := (ManifoldSmoothSmall.manifoldSmoothSmallDegreewiseFunctionIso E A X
    (fun i => (U i : Set X)) n).inv f
  have hb : manifoldSmoothSmallCechNerveAugmentation E X U A n b = bN := by
    change SmallCochainCechComparison.coverCechCochainAugmentation
      (manifoldSmoothSmallSimplexCover E X (fun i => (U i : Set X)) n) A
        ((ManifoldSmoothSmall.manifoldSmoothSmallDegreewiseFunctionIso E A X
          (fun i => (U i : Set X)) n).toLinearEquiv
            ((ManifoldSmoothSmall.manifoldSmoothSmallDegreewiseFunctionIso E A X
              (fun i => (U i : Set X)) n).toLinearEquiv.symm f)) = bN
    rw [LinearEquiv.apply_symm_apply]
    exact hf
  refine ⟨b, ?_⟩
  calc
    _ = manifoldSmoothSmallCechDegreeEquiv E X U A n 0
        (manifoldSmoothSmallCechNerveAugmentation E X U A n b) :=
      (manifoldSmoothSmallCechComparisonIso_augmentation E X U A n b).symm
    _ = manifoldSmoothSmallCechDegreeEquiv E X U A n 0 bN :=
      congrArg (manifoldSmoothSmallCechDegreeEquiv E X U A n 0) hb
    _ = c := (manifoldSmoothSmallCechDegreeEquiv E X U A n 0).apply_symm_apply c

/-- Exactness for the canonical augmentation and the existing smooth
presheaf Čech differential, with no small-to-all comparison assumption. -/
theorem manifoldSmoothSmallCechStandardAugmentation_exact (n : ℕ) :
    Function.Exact (manifoldSmoothSmallCechStandardAugmentation E X U A n)
      (DeRham.Comparison.SmoothCech.cechDelta (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U 0) := by
  intro c
  constructor
  · exact manifoldSmoothSmallCechStandardAugmentation_preimage E X U A n c
  · rintro ⟨b, rfl⟩
    exact manifoldSmoothSmallCechStandardAugmentation_delta E X U A n b

/-- The equivalent kernel/range identity for the same canonical maps. -/
theorem manifoldSmoothSmallCechStandardAugmentation_range (n : ℕ) :
    LinearMap.range (manifoldSmoothSmallCechStandardAugmentation E X U A n) =
      LinearMap.ker (DeRham.Comparison.SmoothCech.cechDelta (ManifoldSmoothPresheaf.manifoldSmoothCochainDegreePresheaf E X A n) U 0) :=
  (LinearMap.exact_iff.mp
    (manifoldSmoothSmallCechStandardAugmentation_exact E X U A n)).symm

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmallCech
