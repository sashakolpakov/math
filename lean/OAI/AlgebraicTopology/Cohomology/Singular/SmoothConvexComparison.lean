import OAI.AlgebraicTopology.Cohomology.Singular.SmoothComparison
import OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen

/-! # Smooth Convex Comparison -/

namespace OAI.AlgebraicTopology.Cohomology.Singular

noncomputable section

/-!
# Smooth singular comparison on nonempty convex domains

The affine contraction stays inside a convex domain and has the previously
proved ambient smooth extension. Consequently the actual restriction from
continuous to smooth singular cochains is a cochain homotopy equivalence.
-/

open _root_.CategoryTheory Opposite MonoidalCategory
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E}

/-- The affine interval coordinate lies in the closed unit interval. -/
theorem SmoothConvexComparison.simplexTimeMap_mem_Icc {n : ℕ} (τ : Fin (n + 1) → Fin 2)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : SmoothHomotopy.simplexTimeMap τ x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [SmoothHomotopy.simplexTimeMap_apply]
  exact ⟨Convexity.StdSimplex.weights_nonneg (w := Convexity.StdSimplex.map τ x) 1,
    Convexity.StdSimplex.weights_apply_le_one (Convexity.StdSimplex.map τ x) 1⟩

/-- The subset-valued affine contraction of a simplex in a convex set. -/
def SmoothConvexComparison.convexContractionSimplex (hU : Convex ℝ U) (c : U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (τ : Fin (n + 1) → Fin 2) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), U) where
  toFun x := ⟨SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ) τ x,
    hU (σ x).property c.property (sub_nonneg.mpr (SmoothConvexComparison.simplexTimeMap_mem_Icc τ x).2)
      (SmoothConvexComparison.simplexTimeMap_mem_Icc τ x).1 (sub_add_cancel 1 _)⟩
  continuous_toFun :=
    (SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ) τ).continuous.subtype_mk _

/-- The subset contraction has exactly the known ambient smooth formula. -/
theorem SmoothConvexComparison.convexContractionSimplex_ambient (hU : Convex ℝ U) (c : U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) (τ : Fin (n + 1) → Fin 2) :
    (SmoothOpen.normedSubsetInclusion U).hom.comp (SmoothConvexComparison.convexContractionSimplex hU c σ τ) =
      SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ) τ := rfl

/-- Affine contraction preserves the actual ambient smooth extension condition. -/
theorem SmoothOpen.IsSmoothSimplexIn.convexContraction (hU : Convex ℝ U) (c : U) {n : ℕ}
    {σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)} (hσ : SmoothOpen.IsSmoothSimplexIn U σ)
    (τ : Fin (n + 1) → Fin 2) :
    SmoothOpen.IsSmoothSimplexIn U (SmoothConvexComparison.convexContractionSimplex hU c σ τ) :=
  hσ.linearContraction (c : E) τ

theorem SmoothConvexComparison.convexContractionSimplex_precomp (hU : Convex ℝ U) (c : U) {m n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U))
    (θ : Fin (m + 1) → Fin (n + 1)) (τ : Fin (n + 1) → Fin 2) :
    SmoothConvexComparison.convexContractionSimplex hU c
        (σ.comp ⟨Convexity.StdSimplex.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩) (τ ∘ θ) =
      (SmoothConvexComparison.convexContractionSimplex hU c σ τ).comp
        ⟨Convexity.StdSimplex.map θ, Convexity.StdSimplex.continuous_map ℝ θ⟩ := by
  ext x
  exact congrArg (fun f : C(Convexity.StdSimplex ℝ (Fin (m + 1)), E) => f x)
    (SmoothHomotopy.linearContractionSimplex_precomp (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ) θ τ)

@[simp]
theorem SmoothConvexComparison.convexContractionSimplex_zero (hU : Convex ℝ U) (c : U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    SmoothConvexComparison.convexContractionSimplex hU c σ (fun _ => 0) = σ := by
  ext x
  change SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ)
    (fun _ => 0) x = (σ x).val
  rw [SmoothHomotopy.linearContractionSimplex_zero]
  rfl

@[simp]
theorem SmoothConvexComparison.convexContractionSimplex_one (hU : Convex ℝ U) (c : U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    SmoothConvexComparison.convexContractionSimplex hU c σ (fun _ => 1) = ContinuousMap.const _ c := by
  ext x
  change SmoothHomotopy.linearContractionSimplex (c : E) ((SmoothOpen.normedSubsetInclusion U).hom.comp σ)
    (fun _ => 1) x = c.val
  rw [SmoothHomotopy.linearContractionSimplex_one]
  rfl

/-- The constant smooth zero-simplex in an arbitrary subset. -/
def SmoothConvexComparison.subsetSmoothPointSimplex (c : U) :
    (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet _⦋0⦌ :=
  ⟨((TopCat.of U).toSSetObjEquiv _).symm (ContinuousMap.const _ c), by
    change Smooth.IsSmoothSimplex (ContinuousMap.const _ (c : E))
    exact Smooth.isSmoothSimplex_const 0 (c : E)⟩

/-- Constant simplicial inverse, up to homotopy, for a convex-domain inclusion. -/
def SmoothConvexComparison.subsetSmoothComparisonRetraction (c : U) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet :=
  SSet.const (SmoothConvexComparison.subsetSmoothPointSimplex c)

/-- The affine contraction as a morphism from the smooth simplicial cylinder. -/
def SmoothConvexComparison.convexSmoothContractionMap (hU : Convex ℝ U) (c : U) :
    (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet ⊗ Δ[1] ⟶
      (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet where
  app n := ↾fun p => ⟨((TopCat.of U).toSSetObjEquiv n).symm
      (SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2)), by
    change SmoothOpen.IsSmoothSimplexIn U
      (SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2))
    exact SmoothOpen.IsSmoothSimplexIn.convexContraction hU c
      (σ := (TopCat.of U).toSSetObjEquiv n p.1.val) p.1.property _⟩
  naturality n m θ := by
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of U).toSSetObjEquiv m).injective
    change SmoothConvexComparison.convexContractionSimplex hU c
        (((TopCat.of U).toSSetObjEquiv n p.1.val).comp
          ⟨Convexity.StdSimplex.map θ.unop, Convexity.StdSimplex.continuous_map ℝ θ.unop⟩)
        ((SSet.stdSimplex.asOrderHom p.2) ∘ θ.unop) =
      (SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.1.val)
        (SSet.stdSimplex.asOrderHom p.2)).comp
          ⟨Convexity.StdSimplex.map θ.unop, Convexity.StdSimplex.continuous_map ℝ θ.unop⟩
    exact SmoothConvexComparison.convexContractionSimplex_precomp hU c _ _ _

/-- The smooth-side composite is simplicially homotopic to identity. -/
def SmoothConvexComparison.convexSmoothComparisonHomotopy (hU : Convex ℝ U) (c : U) :
    SSet.Homotopy (𝟙 (SmoothOpen.subsetSmoothSingularSubcomplex U).toSSet)
      ((SmoothOpen.subsetSmoothSingularSubcomplex U).ι ≫ SmoothConvexComparison.subsetSmoothComparisonRetraction c) where
  h := SmoothConvexComparison.convexSmoothContractionMap hU c
  h₀ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of U).toSSetObjEquiv n).injective
    change SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.val)
      (fun _ => 0) = _
    exact SmoothConvexComparison.convexContractionSimplex_zero hU c _
  h₁ := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.ext_apply
    intro p
    apply Subtype.ext
    apply ((TopCat.of U).toSSetObjEquiv n).injective
    change SmoothConvexComparison.convexContractionSimplex hU c ((TopCat.of U).toSSetObjEquiv n p.val)
      (fun _ => 1) = ContinuousMap.const _ c
    exact SmoothConvexComparison.convexContractionSimplex_one hU c _
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

/-- Ordinary continuous affine contraction inside the convex domain. -/
def SmoothConvexComparison.convexContinuousContraction (hU : Convex ℝ U) (c : U) :
    TopCat.Homotopy (𝟙 (TopCat.of U))
      (TopCat.ofHom (ContinuousMap.const U c)) where
  toFun p := ⟨(1 - (p.1 : ℝ)) • (p.2 : E) + (p.1 : ℝ) • (c : E),
    hU p.2.property c.property (sub_nonneg.mpr p.1.property.2)
      p.1.property.1 (sub_add_cancel 1 _)⟩
  continuous_toFun := by fun_prop
  map_zero_left x := by apply Subtype.ext; simp
  map_one_left x := by apply Subtype.ext; simp

theorem SmoothConvexComparison.subsetSmoothRetraction_inclusion (c : U) :
    SmoothConvexComparison.subsetSmoothComparisonRetraction c ≫ (SmoothOpen.subsetSmoothSingularSubcomplex U).ι =
      TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const U c)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.ext_apply
  intro σ
  apply ((TopCat.of U).toSSetObjEquiv n).injective
  ext x
  rfl

/-- The continuous-side composite is simplicially homotopic to identity. -/
def SmoothConvexComparison.convexContinuousComparisonHomotopy (hU : Convex ℝ U) (c : U) :
    SSet.Homotopy (𝟙 (TopCat.toSSet.obj (TopCat.of U)))
      (SmoothConvexComparison.subsetSmoothComparisonRetraction c ≫ (SmoothOpen.subsetSmoothSingularSubcomplex U).ι) := by
  rw [SmoothConvexComparison.subsetSmoothRetraction_inclusion]
  have h := (SmoothConvexComparison.convexContinuousContraction hU c).toSSet
  rw [TopCat.toSSet.map_id] at h
  exact h

variable {R : Type} [Ring R]

/-- The actual smooth-simplex restriction on a convex domain is a cochain
homotopy equivalence. -/
def SmoothConvexComparison.convexSmoothCochainComparisonHomotopyEquiv (M : ModuleCat.{0} R)
    (hU : Convex ℝ U) (c : U) :
    _root_.HomotopyEquiv (Basic.singularCochains M (TopCat.of U)) (SmoothOpen.subsetSmoothCochains M U) where
  hom := SmoothOpen.subsetSmoothCochainRestriction M U
  inv := Functor.simplicialPullback M (SmoothConvexComparison.subsetSmoothComparisonRetraction c)
  homotopyHomInvId := by
    simpa only [Functor.simplicialPullback_comp, Functor.simplicialPullback_id,
      SmoothOpen.subsetSmoothCochainRestriction] using
      (Singular.Homotopy.simplicialPullbackHomotopy M (SmoothConvexComparison.convexContinuousComparisonHomotopy hU c)).symm
  homotopyInvHomId := by
    simpa only [Functor.simplicialPullback_comp, Functor.simplicialPullback_id,
      SmoothOpen.subsetSmoothCochainRestriction] using
      (Singular.Homotopy.simplicialPullbackHomotopy M (SmoothConvexComparison.convexSmoothComparisonHomotopy hU c)).symm

/-- Genuine smooth-versus-continuous cohomology comparison on a convex domain. -/
def SmoothConvexComparison.convexSmoothCohomologyComparisonIso (M : ModuleCat.{0} R)
    (hU : Convex ℝ U) (c : U) (n : ℕ) :
    Basic.singularCohomology M (TopCat.of U) n ≅ (SmoothOpen.subsetSmoothCochains M U).homology n :=
  (SmoothConvexComparison.convexSmoothCochainComparisonHomotopyEquiv M hU c).toHomologyIso n

@[simp]
theorem SmoothConvexComparison.convexSmoothCohomologyComparisonIso_hom (M : ModuleCat.{0} R)
    (hU : Convex ℝ U) (c : U) (n : ℕ) :
    (SmoothConvexComparison.convexSmoothCohomologyComparisonIso M hU c n).hom =
      HomologicalComplex.homologyMap (SmoothOpen.subsetSmoothCochainRestriction M U) n := rfl

/-- Restriction induces an isomorphism in every degree on a nonempty convex
domain, including every nonempty convex open domain. -/
theorem SmoothConvexComparison.isIso_convexSmoothCohomologyRestriction (M : ModuleCat.{0} R)
    (hU : Convex ℝ U) (hne : U.Nonempty) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SmoothOpen.subsetSmoothCochainRestriction M U) n) := by
  let c : U := ⟨hne.choose, hne.choose_spec⟩
  change IsIso (SmoothConvexComparison.convexSmoothCohomologyComparisonIso M hU c n).hom
  infer_instance

end

end OAI.AlgebraicTopology.Cohomology.Singular
