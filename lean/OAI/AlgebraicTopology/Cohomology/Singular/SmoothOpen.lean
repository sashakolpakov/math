import OAI.AlgebraicTopology.Cohomology.Singular.Smooth
import OAI.AlgebraicTopology.Cohomology.Singular.Functor

/-! # Smooth Open -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen

noncomputable section

/-!
# Smooth singular simplices in subsets and open domains

The simplicial set is constructed by inverse image of the genuine smooth
singular subcomplex under the continuous inclusion of a subset. For an open
subset the extension can be chosen with its values in that open subset; the
equivalence is proved rather than imposed as a hypothesis.
-/

open _root_.CategoryTheory Opposite
open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex Simplicial ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordinary continuous inclusion of a subset into the ambient normed space. -/
def normedSubsetInclusion (U : Set E) : TopCat.of U ⟶ TopCat.of E :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- A simplex in a subset is smooth when its ambient simplex has a genuine
smooth neighborhood extension. -/
def IsSmoothSimplexIn (U : Set E) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) : Prop :=
  Smooth.IsSmoothSimplex ((normedSubsetInclusion U).hom.comp σ)

/-- In an open target the smooth extension itself may be chosen to remain in
the target, by shrinking its open domain. -/
theorem isSmoothSimplexIn_iff_extension {U : Set E} (hU : IsOpen U) {n : ℕ}
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U)) :
    IsSmoothSimplexIn U σ ↔
      ∃ (F : (Fin (n + 1) → ℝ) → E) (V : Set (Fin (n + 1) → ℝ)),
        IsOpen V ∧ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
          (x : Fin (n + 1) → ℝ)) ⊆ V ∧
          ContDiffOn ℝ ∞ F V ∧ Set.MapsTo F V U ∧
            ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)), F x = (σ x).val := by
  constructor
  · rintro ⟨F, V, hV, hsub, hF, heq⟩
    refine ⟨F, V ∩ F ⁻¹' U, hF.continuousOn.isOpen_inter_preimage hV hU,
      ?_, hF.mono Set.inter_subset_left, Set.inter_subset_right, heq⟩
    rintro _ ⟨x, rfl⟩
    refine ⟨hsub ⟨x, rfl⟩, ?_⟩
    change F x ∈ U
    have hxeq := heq x
    change F x = (σ x).val at hxeq
    rw [hxeq]
    exact (σ x).property
  · rintro ⟨F, V, hV, hsub, hF, _, heq⟩
    exact ⟨F, V, hV, hsub, hF, heq⟩

/-- Actual smooth singular simplices in a subset, as a simplicial subcomplex
of the continuous singular simplices of that subset. -/
def subsetSmoothSingularSubcomplex (U : Set E) :
    (TopCat.toSSet.obj (TopCat.of U)).Subcomplex :=
  (Smooth.smoothSingularSubcomplex E).preimage
    (TopCat.toSSet.map (normedSubsetInclusion U))

/-- Inclusion from subset-valued smooth simplices into ambient smooth simplices. -/
def subsetSmoothToAmbient (U : Set E) :
    (subsetSmoothSingularSubcomplex U).toSSet ⟶
      (Smooth.smoothSingularSubcomplex E).toSSet :=
  (Smooth.smoothSingularSubcomplex E).fromPreimage
    (TopCat.toSSet.map (normedSubsetInclusion U))

@[reassoc]
theorem subsetSmoothToAmbient_inclusion (U : Set E) :
    subsetSmoothToAmbient U ≫ Smooth.smoothSingularInclusion E =
      (subsetSmoothSingularSubcomplex U).ι ≫
        TopCat.toSSet.map (normedSubsetInclusion U) := rfl

/-- Ordinary continuous inclusion associated with a containment of subsets. -/
def normedSubsetMap {U V : Set E} (h : U ⊆ V) : TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

/-- Inclusion of targets restricts to their genuine smooth singular simplices. -/
def subsetSmoothMap {U V : Set E} (h : U ⊆ V) :
    (subsetSmoothSingularSubcomplex U).toSSet ⟶
      (subsetSmoothSingularSubcomplex V).toSSet where
  app n := ↾fun σ => ⟨(TopCat.toSSet.map (normedSubsetMap h)).app n σ.val, by
    exact σ.property⟩
  naturality n m f := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((TopCat.toSSet.map (normedSubsetMap h)).naturality f) σ.val

@[reassoc]
theorem subsetSmoothMap_inclusion {U V : Set E} (h : U ⊆ V) :
    subsetSmoothMap h ≫ (subsetSmoothSingularSubcomplex V).ι =
      (subsetSmoothSingularSubcomplex U).ι ≫
        TopCat.toSSet.map (normedSubsetMap h) := rfl

@[simp]
theorem subsetSmoothMap_refl (U : Set E) :
    subsetSmoothMap (Set.Subset.refl U) =
      𝟙 (subsetSmoothSingularSubcomplex U).toSSet := by
  ext n σ
  apply Subtype.ext
  rfl

@[simp]
theorem subsetSmoothMap_comp {U V W : Set E} (h : U ⊆ V) (k : V ⊆ W) :
    subsetSmoothMap (h.trans k) = subsetSmoothMap h ≫ subsetSmoothMap k := by
  ext n σ
  apply Subtype.ext
  rfl

variable {R : Type} [Ring R]

/-- Actual smooth singular cochains in a subset of the normed space. -/
abbrev subsetSmoothCochains (M : ModuleCat.{0} R) (U : Set E) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  Basic.simplicialCochains (subsetSmoothSingularSubcomplex U).toSSet M

/-- Restriction of continuous singular cochains to the smooth simplices. -/
def subsetSmoothCochainRestriction (M : ModuleCat.{0} R) (U : Set E) :
    Basic.singularCochains M (TopCat.of U) ⟶ subsetSmoothCochains M U :=
  Functor.simplicialPullback M (subsetSmoothSingularSubcomplex U).ι

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothOpen
