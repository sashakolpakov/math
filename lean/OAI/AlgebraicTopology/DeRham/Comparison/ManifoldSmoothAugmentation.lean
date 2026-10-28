import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.ConvexResolution
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution

/-! # Manifold Smooth Augmentation -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSmoothAugmentation

noncomputable section

/-!
# Locally constant augmentation into genuine manifold-smooth singular cochains

The augmentation is the literal ordinary singular augmentation followed by
restriction to actual manifold-smooth simplices. On every convex Euclidean
open it is a quasi-isomorphism, including the empty open. The point-evaluation
formula and comparison triangle identify the map without an opaque choice.
-/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open scoped Simplicial ContDiff _root_.Manifold

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {R : Type} [Ring R]

/-- The actual locally constant single-degree augmentation into manifold-smooth cochains. -/
def locallyConstantManifoldSmoothResolutionMap (A : ModuleCat.{0} R)
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] :
    (CochainComplex.single₀ (ModuleCat.{0} R)).obj
      (ModuleCat.of R (LocallyConstant X A)) ⟶ Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E A X :=
  Cohomology.Singular.ConvexResolution.locallyConstantSingularResolutionMap A (TopCat.of X) ≫
    Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E A X

/-- The comparison triangle is the actual composition of the two existing maps. -/
theorem locallyConstantManifoldSmoothResolutionMap_triangle (A : ModuleCat.{0} R)
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] :
    Cohomology.Singular.ConvexResolution.locallyConstantSingularResolutionMap A (TopCat.of X) ≫
      Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E A X =
        locallyConstantManifoldSmoothResolutionMap E A X := rfl

@[simp]
theorem locallyConstantManifoldSmoothResolutionMap_f_zero (A : ModuleCat.{0} R)
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] :
    (locallyConstantManifoldSmoothResolutionMap E A X).f 0 =
      Cohomology.Singular.Augmentation.locallyConstantToSingularZero A (TopCat.of X) ≫
        (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E A X).f 0 := by
  rw [locallyConstantManifoldSmoothResolutionMap, HomologicalComplex.comp_f,
    Cohomology.Singular.ConvexResolution.locallyConstantSingularResolutionMap_f_zero]
  rfl

/-- At every smooth zero-simplex, the augmentation evaluates the locally constant function. -/
theorem locallyConstantManifoldSmoothResolutionMap_apply (A : ModuleCat.{0} R)
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] (f : LocallyConstant X A)
    (s : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).toSSet _⦋0⦌) :
    (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).toSSet A 0).hom
      ((locallyConstantManifoldSmoothResolutionMap E A X).f 0 f) s =
        f (TopCat.toSSetObj₀Equiv ((Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E X).app _ s)) := by
  rw [locallyConstantManifoldSmoothResolutionMap_f_zero]
  change (Cohomology.Singular.Coefficients.degreewiseFunctionIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).toSSet A 0).hom
    ((Cohomology.Singular.Functor.simplicialPullback A (Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E X)).f 0
      (Cohomology.Singular.Augmentation.locallyConstantToSingularZero A (TopCat.of X) f)) s = _
  rw [Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback, ← Cohomology.Singular.Augmentation.singularZeroCochainPointIso_apply_simplex]
  exact Cohomology.Singular.Augmentation.locallyConstantToSingularZero_apply A (TopCat.of X) f _

/-- An empty target has no singular simplices, so its smooth subcomplex is the whole one. -/
theorem manifoldSmoothSingularSubcomplex_eq_top_of_isEmpty
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsEmpty X] :
    Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E X = ⊤ := by
  ext n σ
  exact isEmptyElim ((TopCat.of X).toSSetObjEquiv n σ
    (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n.unop.len + 1))))

/-- Restricting to smooth simplices is an actual isomorphism on an empty target. -/
theorem isIso_manifoldSmoothRestriction_of_isEmpty (A : ModuleCat.{0} R)
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsEmpty X] :
    IsIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E A X) := by
  have : IsIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E X) := by
    change IsIso (SSet.Subcomplex.ι (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E X))
    rw [manifoldSmoothSingularSubcomplex_eq_top_of_isEmpty E X]
    change IsIso (SSet.Subcomplex.topIso (TopCat.toSSet.obj (TopCat.of X))).hom
    infer_instance
  change IsIso ((Cohomology.Singular.Functor.simplicialCochainsFunctor A).map (Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E X).op)
  infer_instance

/-- The verified convex smooth/continuous comparison, now including the empty open. -/
theorem quasiIso_convexOpenManifoldSmoothRestriction (A : ModuleCat.{0} R)
    (U : Opens E) (hU : Convex ℝ (U : Set E)) :
    QuasiIso (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E A U) := by
  by_cases hne : (U : Set E).Nonempty
  · exact Cohomology.Singular.ChartSmoothComparison.quasiIso_convexManifoldSmoothRestriction A U hU hne
  · have : IsEmpty U := ⟨fun x => hne ⟨x.val, x.property⟩⟩
    let := isIso_manifoldSmoothRestriction_of_isEmpty E A U
    infer_instance

/-- The literal locally constant augmentation is a quasi-isomorphism on every
convex Euclidean open, without a nonemptiness hypothesis. -/
theorem locallyConstantManifoldSmoothResolutionMap_quasiIso_convexOpen
    (A : ModuleCat.{0} R) (U : Opens E) (hU : Convex ℝ (U : Set E)) :
    QuasiIso (locallyConstantManifoldSmoothResolutionMap E A U) := by
  let := Cohomology.Singular.ConvexResolution.locallyConstantSingularResolutionMap_quasiIso_convexOpen A U hU
  let := quasiIso_convexOpenManifoldSmoothRestriction E A U hU
  exact quasiIso_comp (Cohomology.Singular.ConvexResolution.locallyConstantSingularResolutionMap A (TopCat.of U))
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E A U)

section Naturality

variable {E}
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable [ChartedSpace E X] [ChartedSpace F Y]

/-- Pullback of locally constant functions and of smooth singular cochains
commutes with this literal augmentation. -/
theorem locallyConstantManifoldSmoothResolutionMap_naturality (A : ModuleCat.{0} R)
    (f : X → Y) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    (CochainComplex.single₀ (ModuleCat.{0} R)).map
        (ModuleCat.ofHom (LocallyConstant.comapₗ R ⟨f, hf.continuous⟩)) ≫
        locallyConstantManifoldSmoothResolutionMap E A X =
      locallyConstantManifoldSmoothResolutionMap F A Y ≫
        Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E F A f hf := by
  rw [locallyConstantManifoldSmoothResolutionMap,
    locallyConstantManifoldSmoothResolutionMap, ← Category.assoc,
    Cohomology.Singular.ConvexResolution.locallyConstantSingularResolutionMap_naturality A
      (TopCat.ofHom ⟨f, hf.continuous⟩), Category.assoc,
    Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothCochainRestriction_naturality A f hf, Category.assoc]

end Naturality

/-- The compatible map of actual presheaf complexes, extending the existing
degree-zero smooth augmentation without redefining it. -/
def locallyConstantManifoldSmoothPresheafResolutionMap
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] :
    (CochainComplex.single₀ ((TopCat.of X).Presheaf (ModuleCat.{0} ℂ))).obj
      (LocallyConstantSheaf.locallyConstantPresheaf (TopCat.of X)) ⟶
        Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X (ModuleCat.of ℂ ℂ) :=
  Cohomology.Singular.ConvexResolution.locallyConstantSingularPresheafResolutionMap (TopCat.of X) ≫
    Cohomology.Singular.SmoothStalkComparison.manifoldSmoothPresheafRestriction E X (ModuleCat.of ℂ ℂ)

@[simp]
theorem locallyConstantManifoldSmoothPresheafResolutionMap_f_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] :
    (locallyConstantManifoldSmoothPresheafResolutionMap E X).f 0 =
      Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothAugmentation E X := by
  rw [locallyConstantManifoldSmoothPresheafResolutionMap, HomologicalComplex.comp_f,
    Cohomology.Singular.ConvexResolution.locallyConstantSingularPresheafResolutionMap_f_zero]
  rfl

/-- The new object-level augmentation and the previously defined presheaf
augmentation agree literally on every open set in degree zero. -/
theorem locallyConstantManifoldSmoothResolutionMap_f_zero_eq_presheaf
    (X : Type) [TopologicalSpace X] [ChartedSpace E X] (U : Opens X) :
    (locallyConstantManifoldSmoothResolutionMap E (ModuleCat.of ℂ ℂ) U).f 0 =
      (Cohomology.Singular.SmoothSheafResolution.locallyConstantManifoldSmoothAugmentation E X).app (op U) := by
  rw [locallyConstantManifoldSmoothResolutionMap_f_zero]
  rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSmoothAugmentation
