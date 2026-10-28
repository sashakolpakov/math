import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Manifold Smooth Simplex Composition -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Composition with the genuine smooth standard-simplex model

A subset-smooth simplex into a standard simplex has an ambient smooth
extension. To compose with a manifold-smooth simplex, restrict that extension
to the inverse image of the latter's extension neighborhood. This constructs
the needed neighborhood explicitly, including at the boundary of the simplex.

The resulting simplicial maps transport actual smooth model chains to smooth
singular chains. Their formulas and naturality use ordinary composition of
the underlying continuous simplex maps.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff _root_.Manifold

/-- The barycentric coordinates of the standard simplex as a continuous map. -/
def ManifoldSmoothSimplexComposition.simplexCoordinateMap (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), Fin (n + 1) → ℝ) :=
  ⟨fun x => x.weights, continuous_pi fun i =>
    Convexity.StdSimplex.continuous_weights_apply ℝ i⟩

/-- A map into a standard simplex is smooth when its coordinates extend smoothly. -/
def ManifoldSmoothSimplexComposition.IsSmoothSimplexMap {m n : ℕ}
    (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1)))) : Prop :=
  Smooth.IsSmoothSimplex ((ManifoldSmoothSimplexComposition.simplexCoordinateMap n).comp τ)

/-- The smooth singular model of a standard simplex, defined through its coordinates. -/
def ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))))).Subcomplex :=
  (Smooth.smoothSingularSubcomplex (Fin (n + 1) → ℝ)).preimage
    (TopCat.toSSet.map (TopCat.ofHom (ManifoldSmoothSimplexComposition.simplexCoordinateMap n)))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- Composition of neighborhood-smooth simplices is neighborhood-smooth.
The inner simplex takes its values in the standard simplex of the outer one. -/
theorem Smooth.IsSmoothSimplex.comp {m n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E)} (hσ : Smooth.IsSmoothSimplex σ)
    {τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))}
    (hτ : ManifoldSmoothSimplexComposition.IsSmoothSimplexMap τ) :
    Smooth.IsSmoothSimplex (σ.comp τ) := by
  rcases hσ with ⟨F, U, hU, hsubU, hF, hFeq⟩
  rcases hτ with ⟨G, V, hV, hsubV, hG, hGeq⟩
  refine ⟨F ∘ G, V ∩ G ⁻¹' U, hG.continuousOn.isOpen_inter_preimage hV hU,
    ?_, hF.comp (hG.mono Set.inter_subset_left) Set.inter_subset_right, ?_⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨hsubV ⟨x, rfl⟩, ?_⟩
    change G x ∈ U
    rw [hGeq x]
    exact hsubU ⟨τ x, rfl⟩
  · intro x
    exact (congrArg F (hGeq x)).trans (hFeq (τ x))

/-- Composition also preserves actual smooth simplices valued in an arbitrary
subset; no openness of the target subset is required. -/
theorem SmoothOpen.IsSmoothSimplexIn.comp {U : Set E} {m n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)} (hσ : SmoothOpen.IsSmoothSimplexIn U σ)
    {τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))}
    (hτ : ManifoldSmoothSimplexComposition.IsSmoothSimplexMap τ) :
    SmoothOpen.IsSmoothSimplexIn U (σ.comp τ) :=
  Smooth.IsSmoothSimplex.comp hσ hτ

/-- A manifold-smooth simplex composes with a subset-smooth simplex into its
standard-simplex domain, using an explicitly restricted smooth neighborhood. -/
theorem ManifoldSmooth.IsManifoldSmoothSimplex.comp {m n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)} (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    {τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1)))}
    (hτ : ManifoldSmoothSimplexComposition.IsSmoothSimplexMap τ) :
    ManifoldSmooth.IsManifoldSmoothSimplex E (σ.comp τ) := by
  rcases hσ with ⟨F, U, hU, hsubU, hF, hFeq⟩
  rcases hτ with ⟨G, V, hV, hsubV, hG, hGeq⟩
  refine ⟨F ∘ G, V ∩ G ⁻¹' U, hG.continuousOn.isOpen_inter_preimage hV hU,
    ?_, hF.comp (hG.mono Set.inter_subset_left).contMDiffOn Set.inter_subset_right, ?_⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨hsubV ⟨x, rfl⟩, ?_⟩
    change G x ∈ U
    rw [hGeq x]
    exact hsubU ⟨τ x, rfl⟩
  · intro x
    exact (congrArg F (hGeq x)).trans (hFeq (τ x))

/-- Smooth maps between standard simplices are closed under composition. -/
theorem ManifoldSmoothSimplexComposition.IsSmoothSimplexMap.comp {k m n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)),
      Convexity.StdSimplex ℝ (Fin (k + 1)))} (hσ : ManifoldSmoothSimplexComposition.IsSmoothSimplexMap σ)
    {τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1)))} (hτ : ManifoldSmoothSimplexComposition.IsSmoothSimplexMap τ) :
    ManifoldSmoothSimplexComposition.IsSmoothSimplexMap (σ.comp τ) :=
  Smooth.IsSmoothSimplex.comp hσ hτ

/-- Postcomposition by a smooth simplex map preserves the smooth simplex model. -/
def ManifoldSmoothSimplexComposition.simplexSmoothSimplexMap {m n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (m + 1)),
      Convexity.StdSimplex ℝ (Fin (n + 1)))) (hσ : ManifoldSmoothSimplexComposition.IsSmoothSimplexMap σ) :
    (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex m).toSSet ⟶
      (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).toSSet where
  app k := ↾fun τ => ⟨(TopCat.toSSet.map (TopCat.ofHom σ)).app k τ.val, by
    exact ManifoldSmoothSimplexComposition.IsSmoothSimplexMap.comp hσ
      (τ := (TopCat.of (Convexity.StdSimplex ℝ (Fin (m + 1)))).toSSetObjEquiv k τ.val)
      τ.property⟩
  naturality k l f := by
    ext τ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.map (TopCat.ofHom σ)).naturality f) τ.val

/-- Composition by a subset-valued smooth simplex defines a genuine
simplicial map from its smooth standard-simplex model. -/
def ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap {U : Set E} {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (hσ : SmoothOpen.IsSmoothSimplexIn U σ) :
    (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).toSSet ⟶
      (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet where
  app k := ↾fun τ => ⟨(TopCat.toSSet.map (TopCat.ofHom σ)).app k τ.val, by
    exact SmoothOpen.IsSmoothSimplexIn.comp hσ
      (τ := (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv k τ.val) τ.property⟩
  naturality k l f := by
    ext τ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.map (TopCat.ofHom σ)).naturality f) τ.val

/-- Composition by a manifold-smooth simplex defines a genuine simplicial map
from its smooth standard-simplex model into manifold-smooth singular simplices. -/
def ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ) :
    (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).toSSet ⟶
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet where
  app k := ↾fun τ => ⟨(TopCat.toSSet.map (TopCat.ofHom σ)).app k τ.val, by
    exact ManifoldSmooth.IsManifoldSmoothSimplex.comp hσ
      (τ := (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv k τ.val) τ.property⟩
  naturality k l f := by
    ext τ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.map (TopCat.ofHom σ)).naturality f) τ.val

@[simp]
theorem ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap_app_val {U : Set E} {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (hσ : SmoothOpen.IsSmoothSimplexIn U σ)
    (k : SimplexCategoryᵒᵖ)
    (τ : (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).obj k) :
    ((ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap σ hσ).app k τ).val =
      (TopCat.toSSet.map (TopCat.ofHom σ)).app k τ.val := rfl

@[simp]
theorem ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap_app_val {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    (k : SimplexCategoryᵒᵖ)
    (τ : (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).obj k) :
    ((ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap σ hσ).app k τ).val =
      (TopCat.toSSet.map (TopCat.ofHom σ)).app k τ.val := rfl

/-- The induced subset simplex is ordinary pointwise composition. -/
@[simp]
theorem ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap_apply {U : Set E} {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (hσ : SmoothOpen.IsSmoothSimplexIn U σ)
    (k : SimplexCategoryᵒᵖ)
    (τ : (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).obj k)
    (x : Convexity.StdSimplex ℝ (Fin (k.unop.len + 1))) :
    (TopCat.of U).toSSetObjEquiv k ((ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap σ hσ).app k τ).val x =
      σ ((TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv k τ.val x) := rfl

/-- The induced manifold simplex is ordinary pointwise composition. -/
@[simp]
theorem ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap_apply {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    (k : SimplexCategoryᵒᵖ)
    (τ : (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).obj k)
    (x : Convexity.StdSimplex ℝ (Fin (k.unop.len + 1))) :
    (TopCat.of M).toSSetObjEquiv k ((ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap σ hσ).app k τ).val x =
      σ ((TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv k τ.val x) := rfl

/-- Forgetting subset smoothness commutes with the simplex composition map. -/
@[reassoc]
theorem ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap_inclusion {U : Set E} {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (hσ : SmoothOpen.IsSmoothSimplexIn U σ) :
    ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap σ hσ ≫ (SmoothOpen.subsetSmoothSingularSubcomplex U).ι =
      (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).ι ≫
        TopCat.toSSet.map (TopCat.ofHom σ) := rfl

/-- Forgetting manifold smoothness commutes with the simplex composition map. -/
@[reassoc]
theorem ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap_inclusion {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ) :
    ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap σ hσ ≫ ManifoldSmooth.manifoldSmoothInclusion E M =
      (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).ι ≫
        TopCat.toSSet.map (TopCat.ofHom σ) := rfl

/-- The identity simplex has its identity ambient extension. -/
theorem ManifoldSmoothSimplexComposition.isSmoothSimplexIn_stdSimplex_id (n : ℕ) :
    ManifoldSmoothSimplexComposition.IsSmoothSimplexMap
      (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 1)))) :=
  ⟨id, Set.univ, isOpen_univ, Set.subset_univ _, contDiffOn_id, fun _ => rfl⟩

@[simp]
theorem ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap_id (n : ℕ) :
    ManifoldSmoothSimplexComposition.simplexSmoothSimplexMap (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 1))))
        (ManifoldSmoothSimplexComposition.isSmoothSimplexIn_stdSimplex_id n) =
      𝟙 (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).toSSet := by
  ext k τ
  apply Subtype.ext
  rfl

/-- Naturality in a smooth parameter simplex, including simplex face maps. -/
theorem ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap_comp {U : Set E} {m n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (hσ : SmoothOpen.IsSmoothSimplexIn U σ)
    (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hτ : ManifoldSmoothSimplexComposition.IsSmoothSimplexMap τ) :
    ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap (σ.comp τ) (SmoothOpen.IsSmoothSimplexIn.comp hσ hτ) =
      ManifoldSmoothSimplexComposition.simplexSmoothSimplexMap τ hτ ≫ ManifoldSmoothSimplexComposition.subsetSmoothSimplexMap σ hσ := by
  ext k ρ
  apply Subtype.ext
  rfl

/-- Manifold simplex composition is natural in every smooth parameter simplex. -/
theorem ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap_comp {m n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    (τ : C(Convexity.StdSimplex ℝ (Fin (m + 1)), Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hτ : ManifoldSmoothSimplexComposition.IsSmoothSimplexMap τ) :
    ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap (σ.comp τ) (ManifoldSmooth.IsManifoldSmoothSimplex.comp hσ hτ) =
      ManifoldSmoothSimplexComposition.simplexSmoothSimplexMap τ hτ ≫ ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap σ hσ := by
  ext k ρ
  apply Subtype.ext
  rfl

/-- Every standard simplex operator has the usual continuous linear extension. -/
theorem ManifoldSmoothSimplexComposition.isSmoothSimplexIn_stdSimplexMap {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) :
    ManifoldSmoothSimplexComposition.IsSmoothSimplexMap
      ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ :=
  ⟨Smooth.simplexLinearMap f, Set.univ, isOpen_univ, Set.subset_univ _,
    (Smooth.simplexLinearMap f).contDiff.contDiffOn, fun x => Smooth.simplexLinearMap_weights f x⟩

/-- The actual smooth model map associated with a standard simplex operator. -/
def ManifoldSmoothSimplexComposition.smoothSimplexModelMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex m).toSSet ⟶
      (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).toSSet :=
  ManifoldSmoothSimplexComposition.simplexSmoothSimplexMap ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩
    (ManifoldSmoothSimplexComposition.isSmoothSimplexIn_stdSimplexMap f)

/-- The composition map commutes with every standard simplex operator, with
the same precomposition proof used by the manifold smooth subcomplex. -/
theorem ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap_precomp {m n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    (f : Fin (m + 1) → Fin (n + 1)) :
    ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap (σ.comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩)
        (ManifoldSmooth.IsManifoldSmoothSimplex.precomp E hσ f) =
      ManifoldSmoothSimplexComposition.smoothSimplexModelMap f ≫ ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap σ hσ :=
  ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap_comp σ hσ
    ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ (ManifoldSmoothSimplexComposition.isSmoothSimplexIn_stdSimplexMap f)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {N : Type} [TopologicalSpace N] [ChartedSpace F N]

/-- Composition of a smooth parameter simplex is natural under globally smooth
maps of the target manifolds. -/
theorem ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap_postcomp {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), M)) (hσ : ManifoldSmooth.IsManifoldSmoothSimplex E σ)
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap ((⟨f, hf.continuous⟩ : C(M, N)).comp σ)
        (ManifoldSmooth.IsManifoldSmoothSimplex.postcomp hσ hf) =
      ManifoldSmoothSimplexComposition.manifoldSmoothSimplexMap σ hσ ≫ ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf := by
  ext k τ
  apply Subtype.ext
  rfl

/-- The coordinate realization of the finite standard simplex. -/
def ManifoldSmoothSimplexComposition.simplexCoordinateRange (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) => (x.weights : Fin (n + 1) → ℝ))

/-- The native smooth simplex model agrees with the smooth model of its coordinate range. -/
def ManifoldSmoothSimplexComposition.simplexSmoothCoordinatesIso (n : ℕ) :
    (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).toSSet ≅
      (SmoothOpen.subsetSmoothSingularSubcomplex (ManifoldSmoothSimplexComposition.simplexCoordinateRange n)).toSSet := by
  let e : Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ ManifoldSmoothSimplexComposition.simplexCoordinateRange n :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).toHomeomorph
  let ec : C(Convexity.StdSimplex ℝ (Fin (n + 1)), ManifoldSmoothSimplexComposition.simplexCoordinateRange n) :=
    ⟨e, e.continuous⟩
  let ei : C(ManifoldSmoothSimplexComposition.simplexCoordinateRange n, Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    ⟨e.symm, e.symm.continuous⟩
  let p : TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶
      TopCat.of (ManifoldSmoothSimplexComposition.simplexCoordinateRange n) := TopCat.ofHom ec
  let q : TopCat.of (ManifoldSmoothSimplexComposition.simplexCoordinateRange n) ⟶
      TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1))) := TopCat.ofHom ei
  have hinv (k : SimplexCategoryᵒᵖ)
      (σ : (SmoothOpen.subsetSmoothSingularSubcomplex (ManifoldSmoothSimplexComposition.simplexCoordinateRange n)).obj k) :
      (TopCat.toSSet.map q).app k σ.val ∈ (ManifoldSmoothSimplexComposition.simplexSmoothSingularSubcomplex n).obj k := by
    let τ := (TopCat.of (ManifoldSmoothSimplexComposition.simplexCoordinateRange n)).toSSetObjEquiv k σ.val
    change Smooth.IsSmoothSimplex ((ManifoldSmoothSimplexComposition.simplexCoordinateMap n).comp (ei.comp τ))
    have heq : (ManifoldSmoothSimplexComposition.simplexCoordinateMap n).comp (ei.comp τ) =
        (SmoothOpen.normedSubsetInclusion (ManifoldSmoothSimplexComposition.simplexCoordinateRange n)).hom.comp τ := by
      apply ContinuousMap.ext
      intro x
      exact congrArg Subtype.val (e.apply_symm_apply (τ x))
    rw [heq]
    exact σ.property
  refine
    { hom :=
        { app := fun k => ↾fun σ => ⟨(TopCat.toSSet.map p).app k σ.val, σ.property⟩
          naturality := by
            intro k l f
            ext σ
            apply Subtype.ext
            exact ConcreteCategory.congr_hom ((TopCat.toSSet.map p).naturality f) σ.val }
      inv :=
        { app := fun k => ↾fun σ => ⟨(TopCat.toSSet.map q).app k σ.val, hinv k σ⟩
          naturality := by
            intro k l f
            ext σ
            apply Subtype.ext
            exact ConcreteCategory.congr_hom ((TopCat.toSSet.map q).naturality f) σ.val }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext k σ
    apply Subtype.ext
    apply ((TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv k).injective
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply _
  · ext k σ
    apply Subtype.ext
    apply ((TopCat.of (ManifoldSmoothSimplexComposition.simplexCoordinateRange n)).toSSetObjEquiv k).injective
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply _

end

end OAI.AlgebraicTopology.Cohomology.Singular
