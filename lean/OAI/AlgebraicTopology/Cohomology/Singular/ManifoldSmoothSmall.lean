import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf
import OAI.AlgebraicTopology.Cohomology.Singular.Formulas
import OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularCochains

/-! # Manifold Smooth Small -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall

noncomputable section

/-!
# Actual cover-small manifold-smooth singular simplices

The small smooth simplicial set is the intersection of the two existing
subcomplexes of ordinary singular simplices: cover-small simplices and
manifold-smooth simplices with a genuine neighborhood extension. Its
cochains and restrictions are obtained from the actual simplicial maps.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.SmallSingularCochains
open scoped Simplicial _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

section Simplices

variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Set X)

/-- The actual intersection of cover-small and manifold-smooth singular
subcomplexes. Smallness is the first membership condition. -/
def manifoldSmoothSmallSubcomplex : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex (TopCat.of X) U ⊓ ManifoldSmooth.manifoldSmoothSingularSubcomplex E X

/-- Membership has exactly the two standard, already defined meanings. -/
@[simp]
theorem mem_manifoldSmoothSmallSubcomplex {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    σ ∈ (manifoldSmoothSmallSubcomplex E X U).obj n ↔
      (∃ i, Set.range ((TopCat.of X).toSSetObjEquiv n σ) ⊆ U i) ∧
        ManifoldSmooth.IsManifoldSmoothSimplex E ((TopCat.of X).toSSetObjEquiv n σ) := Iff.rfl

/-- The genuine degreewise small smooth simplex type. -/
abbrev ManifoldSmoothSmallSimplex (n : ℕ) : Type :=
  (manifoldSmoothSmallSubcomplex E X U).toSSet _⦋n⦌

/-- The canonical inclusion into all manifold-smooth singular simplices. -/
abbrev manifoldSmoothSmallInclusion :
    (manifoldSmoothSmallSubcomplex E X U).toSSet ⟶
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).toSSet :=
  SSet.Subcomplex.homOfLE inf_le_right

/-- The canonical map forgetting smoothness and retaining smallness. -/
abbrev manifoldSmoothSmallToContinuousSmall :
    (manifoldSmoothSmallSubcomplex E X U).toSSet ⟶
      (DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex (TopCat.of X) U).toSSet :=
  SSet.Subcomplex.homOfLE inf_le_left

/-- The canonical ambient inclusion of the actual intersection. -/
abbrev manifoldSmoothSmallAmbientInclusion :
    (manifoldSmoothSmallSubcomplex E X U).toSSet ⟶ TopCat.toSSet.obj (TopCat.of X) :=
  (manifoldSmoothSmallSubcomplex E X U).ι

@[simp, reassoc]
theorem manifoldSmoothSmallInclusion_ambient :
    manifoldSmoothSmallInclusion E X U ≫ ManifoldSmooth.manifoldSmoothInclusion E X =
      manifoldSmoothSmallAmbientInclusion E X U := rfl

@[simp, reassoc]
theorem manifoldSmoothSmallToContinuousSmall_ambient :
    manifoldSmoothSmallToContinuousSmall E X U ≫ DeRham.Comparison.SmallSingularSet.smallSingularInclusion (TopCat.of X) U =
      manifoldSmoothSmallAmbientInclusion E X U := rfl

/-- The inclusion sends the actual underlying singular simplex to itself. -/
@[simp]
theorem manifoldSmoothSmallInclusion_app_val (n : SimplexCategoryᵒᵖ)
    (σ : (manifoldSmoothSmallSubcomplex E X U).obj n) :
    ((manifoldSmoothSmallInclusion E X U).app n σ).val = σ.val := rfl

/-- The chain map to which the smooth subdivision comparison applies. -/
abbrev manifoldSmoothSmallIntegralChainInclusion :
    (manifoldSmoothSmallSubcomplex E X U).toSSet.chainComplex (ModuleCat.of ℤ ℤ) ⟶
      (ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).toSSet.chainComplex (ModuleCat.of ℤ ℤ) :=
  SSet.chainComplexMap (manifoldSmoothSmallInclusion E X U) (ModuleCat.of ℤ ℤ)

end Simplices

section Cochains

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Set X)

/-- Cochains of the actual cover-small manifold-smooth simplicial set. -/
abbrev manifoldSmoothSmallCochains : CochainComplex (ModuleCat.{0} R) ℕ :=
  Basic.simplicialCochains (manifoldSmoothSmallSubcomplex E X U).toSSet A

/-- The corresponding cohomology object, with no comparison assumption. -/
abbrev manifoldSmoothSmallCohomology (n : ℕ) : ModuleCat.{0} R :=
  (manifoldSmoothSmallCochains E A X U).homology n

/-- Restrict all smooth cochains to the actual cover-small smooth simplices. -/
def manifoldSmoothSmallRestriction :
    ManifoldSmooth.manifoldSmoothCochains E A X ⟶ manifoldSmoothSmallCochains E A X U :=
  Functor.simplicialPullback A (manifoldSmoothSmallInclusion E X U)

/-- Restrict ordinary cover-small cochains to their smooth simplices. -/
def continuousSmallToManifoldSmoothRestriction :
    DeRham.Comparison.SmallSingularCochains.smallSingularCochains A (TopCat.of X) U ⟶ manifoldSmoothSmallCochains E A X U :=
  Functor.simplicialPullback A (manifoldSmoothSmallToContinuousSmall E X U)

/-- The two orders of ordinary-to-smooth and all-to-small restriction agree. -/
@[reassoc]
theorem manifoldSmoothSmallRestriction_square :
    ManifoldSmooth.manifoldSmoothCochainRestriction E A X ≫ manifoldSmoothSmallRestriction E A X U =
      DeRham.Comparison.SmallSingularCochains.smallSingularRestriction A (TopCat.of X) U ≫
        continuousSmallToManifoldSmoothRestriction E A X U := by
  rw [ManifoldSmooth.manifoldSmoothCochainRestriction, manifoldSmoothSmallRestriction,
    DeRham.Comparison.SmallSingularCochains.smallSingularRestriction, continuousSmallToManifoldSmoothRestriction,
    ← Functor.simplicialPullback_comp, ← Functor.simplicialPullback_comp,
    manifoldSmoothSmallInclusion_ambient, manifoldSmoothSmallToContinuousSmall_ambient]

/-- Each degree is literally the module of all coefficient-valued functions
on actual small smooth simplices, through the existing cochain coordinates. -/
def manifoldSmoothSmallDegreewiseFunctionIso (n : ℕ) :
    (manifoldSmoothSmallCochains E A X U).X n ≅
      ModuleCat.of R (ManifoldSmoothSmallSimplex E X U n → A) :=
  Coefficients.degreewiseFunctionIso (manifoldSmoothSmallSubcomplex E X U).toSSet A n

/-- Restriction evaluates the original cochain on the same smooth simplex. -/
theorem manifoldSmoothSmallRestriction_evaluation (n : ℕ)
    (c : (ManifoldSmooth.manifoldSmoothCochains E A X).X n)
    (σ : ManifoldSmoothSmallSimplex E X U n) :
    (manifoldSmoothSmallDegreewiseFunctionIso E A X U n).hom
      ((manifoldSmoothSmallRestriction E A X U).f n c) σ =
        (Coefficients.degreewiseFunctionIso (ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).toSSet A n).hom c
          ((manifoldSmoothSmallInclusion E X U).app (op ⦋n⦌) σ) :=
  Formulas.degreewiseFunctionIso_pullback A (manifoldSmoothSmallInclusion E X U) c σ

end Cochains

section OpenLocalMaps

variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Opens X)

/-- Smooth simplices in a cover member include canonically into the actual
small smooth intersection simplicial set. -/
def manifoldSmoothSmallLocalMap (i : ι) :
    (ManifoldSmooth.manifoldSmoothSingularSubcomplex E (U i)).toSSet ⟶
      (manifoldSmoothSmallSubcomplex E X (fun j => (U j : Set X))).toSSet where
  app n := ↾fun σ =>
    ⟨((ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Subtype.val : U i → X)
      (contMDiff_subtype_val (I := 𝓘(ℝ, E)))).app n σ).val,
      ⟨⟨i, by
        rintro _ ⟨t, rfl⟩
        exact (((TopCat.of (U i)).toSSetObjEquiv n σ.val) t).property⟩,
        ((ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Subtype.val : U i → X)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E)))).app n σ).property⟩⟩
  naturality n m f := by
    apply ConcreteCategory.ext_apply
    intro σ
    apply Subtype.ext
    exact congrArg (fun τ : (ManifoldSmooth.manifoldSmoothSingularSubcomplex E X).obj m => τ.val)
      (ConcreteCategory.congr_hom
        ((ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Subtype.val : U i → X)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E)))).naturality f) σ)

/-- Forgetting cover-smallness recovers the actual smooth open inclusion. -/
@[simp, reassoc]
theorem manifoldSmoothSmallLocalMap_inclusion (i : ι) :
    manifoldSmoothSmallLocalMap E X U i ≫
      manifoldSmoothSmallInclusion E X (fun j => (U j : Set X)) =
        ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Subtype.val : U i → X)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E))) := rfl

end OpenLocalMaps

variable {R : Type} [Ring R] (A : ModuleCat.{0} R)
variable (X : Type) [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Opens X)

/-- Restrict an actual small smooth cochain to one open cover member. -/
def manifoldSmoothSmallLocalRestriction (i : ι) :
    manifoldSmoothSmallCochains E A X (fun j => (U j : Set X)) ⟶
      ManifoldSmooth.manifoldSmoothCochains E A (U i) :=
  Functor.simplicialPullback A (manifoldSmoothSmallLocalMap E X U i)

/-- Restricting first to small smooth simplices and then locally is the
ordinary smooth pullback along the actual open inclusion. -/
@[reassoc]
theorem manifoldSmoothSmallRestriction_local (i : ι) :
    manifoldSmoothSmallRestriction E A X (fun j => (U j : Set X)) ≫
      manifoldSmoothSmallLocalRestriction E A X U i =
        ManifoldSmoothFunctor.manifoldSmoothPullback E E A (Subtype.val : U i → X)
          (contMDiff_subtype_val (I := 𝓘(ℝ, E))) := by
  rw [manifoldSmoothSmallRestriction, manifoldSmoothSmallLocalRestriction,
    ← Functor.simplicialPullback_comp, manifoldSmoothSmallLocalMap_inclusion]
  rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothSmall
