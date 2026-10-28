/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.ComponentSingularClosedFiltration
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Component Singular Ge -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Ambient closed supports for singular-component localization induction

-/

/-! ### Constructions used only in proofs -/

section

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This is the length of the finite list defining the filtration; all terms from this
index onward are empty. -/
abbrev Cycle.ComponentSingularGe.cycleComponentSingularFiltrationLength : ℕ :=
  (AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This smooth scheme is the stratum `S_k \ S_{k+1}` with its induced reduced structure. -/
abbrev Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum (k : ℕ) : Scheme :=
  Stratification.BasicLe.reducedClosedSmoothPiece (Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k)

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This morphism is the inclusion of the smooth stratum `S_k \ S_{k+1}` into `X`. -/
def Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι (k : ℕ) :
    Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum X x k ⟶ X.left :=
  Stratification.BasicLe.reducedClosedSmoothPieceι (Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k) ≫ Cycle.Support.cycleComponentι X.left x

/-- A singular-filtration stratum with its induced structure map to `Spec ℂ`. -/
abbrev Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOver (k : ℕ) : Over (Spec ↧ℂ) :=
  Over.mk (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)

/-- The stratum immersion bundled over `Spec ℂ`. -/
def Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOverι (k : ℕ) :
    Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOver X x k ⟶ X :=
  Over.homMk (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k) rfl

instance Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOverι_isImmersion (k : ℕ) :
    IsImmersion (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOverι X x k).left := by
  change IsImmersion (Stratification.BasicLe.reducedClosedSmoothPieceι (Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k) ≫ Cycle.Support.cycleComponentι X.left x)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι_isImmersion (k : ℕ) :
    IsImmersion (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k) := by
  dsimp [Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι]
  infer_instance

instance Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum_smooth (k : ℕ) :
    Smooth (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k ≫ X.hom) := by
  change Smooth ((Stratification.BasicLe.reducedClosedSmoothPieceι (Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k) ≫ Cycle.Support.cycleComponentι X.left x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

instance Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOver X x k).hom := by
  change LocallyOfFiniteType (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
/-- The successive ambient difference is precisely the image of the smooth stratum. -/
theorem Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_layer (k : ℕ) :
    Set.range (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k) =
      (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k : Set X.left) \
        (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x (k + 1) : Set X.left) := by
  rw [Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Stratification.ClosedFiltration.reducedSmoothClosedFiltration_layer]
  exact Set.image_sdiff (Cycle.Support.cycleComponentι X.left x).isClosedEmbedding.injective _ _

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This open subscheme is `X \ S_{k+1}`, in which the `k`-th stratum is closed. -/
def Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen (k : ℕ) : X.left.Opens :=
  (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x (k + 1)).compl

/-- Let `X` be a smooth integral projective complex scheme and `Z` the reduced closure of `x ∈ X`.
Put `S₀ = Z_sing` and `S_{k+1} = (S_k)_sing`, giving each closed subset its reduced scheme
structure. This is the inclusion of the smooth stratum `S_k \ S_{k+1}` into the open subscheme
`X \ S_{k+1}`. -/
def Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift (k : ℕ) :
    Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum X x k ⟶
      Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k :=
  IsOpenImmersion.lift (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι
    (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k) (by
      rw [Scheme.Opens.range_ι]
      intro y hy
      exact ((Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_layer X x k).le hy).2)

/-- The localization open with its induced structure map to `Spec ℂ`. -/
abbrev Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver (k : ℕ) : Over (Spec ↧ℂ) :=
  ComplexPoint.Basic.ComplexSchemePoint.openScheme X (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k)

instance Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver_locallyOfFiniteType (k : ℕ) :
    LocallyOfFiniteType (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver X x k).hom := by
  change LocallyOfFiniteType
    ((Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom)
  infer_instance

omit [IsIntegral X.left] [Smooth X.hom] in
@[reassoc (attr := simp)]
theorem Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_ι (k : ℕ) :
    Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k ≫
      (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι =
        Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The closed stratum lift bundled over `Spec ℂ`. -/
def Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLiftOver (k : ℕ) :
    Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOver X x k ⟶
      Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver X x k :=
  Over.homMk (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k) (by
    change Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k ≫
      ((Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) =
        Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k ≫ X.hom
    rw [← Category.assoc, Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_ι])

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Its closed image is exactly the restriction of the current support to that open. -/
theorem Cycle.ComponentSingularGe.range_cycleComponentSingularStratumClosedLift (k : ℕ) :
    Set.range (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k) =
      (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι ⁻¹'
        (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k : Set X.left) := by
  have hf (w : Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum X x k) :
      (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι
        (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k w) =
          Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k w :=
    congrArg (fun f => f w) (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_ι X x k)
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ((Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_layer X x k).le ⟨w, (hf w).symm⟩).1
  · intro hy
    obtain ⟨w, hw⟩ := (Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_layer X x k).ge ⟨hy, y.2⟩
    exact ⟨w, (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι.isOpenEmbedding.injective
      ((hf w).trans hw)⟩

/-- Each layer is a closed immersion in precisely the open needed by localization. -/
instance Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k) := by
  have : IsPreimmersion (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k ≫
      (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι) := by
    rw [Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_ι]
    infer_instance
  let : IsPreimmersion (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k) :=
    .of_comp (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k)
      (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι
  apply IsClosedImmersion.of_isPreimmersion
  rw [Cycle.ComponentSingularGe.range_cycleComponentSingularStratumClosedLift]
  exact (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k).isClosed.preimage
    (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι.continuous

instance Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLiftOver_isClosedImmersion (k : ℕ) :
    IsClosedImmersion (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLiftOver X x k).left := by
  change IsClosedImmersion (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k)
  infer_instance

/-- The localization open remains smooth of the original ambient dimension. -/
instance Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen_smoothOfRelativeDimension
    (k d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    SmoothOfRelativeDimension d ((Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) := by
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d
    (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι X.hom

instance Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_smooth (k : ℕ) :
    Smooth (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k ≫
      (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k).ι ≫ X.hom) := by
  rw [← Category.assoc, Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift_ι]
  infer_instance

/-- The smooth-locus immersion into the ambient variety, bundled over `Spec ℂ`. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOverι : ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x ⟶ X :=
  Over.homMk ((Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    Cycle.Support.cycleComponentι X.left x) rfl

instance ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOverι_isImmersion :
    IsImmersion (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOverι X x).left := by
  change IsImmersion ((Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    Cycle.Support.cycleComponentι X.left x)
  infer_instance

end

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

theorem Cycle.ComponentSingularGe.cycleComponentSingularClosedFiltration_length :
    Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x
      (AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length = ⊥ := by
  let := Cycle.SupportEq.cycleComponent_isNoetherian X x
  exact Stratification.ClosedFiltration.reducedSmoothClosedFiltration_length _ _

omit [IsIntegral X.left] [Smooth X.hom] in
theorem Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_antitone :
    Antitone (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x) :=
  fun _ _ hkl ↦ Set.image_mono (Stratification.ClosedFiltration.reducedSmoothClosedFiltration_antitone _ _ hkl)

theorem Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_length :
    Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x
      (AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length = ⊥ := by
  apply SetLike.coe_injective
  change Cycle.Support.cycleComponentι X.left x ''
    (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x
      (AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length : Set _) = ∅
  rw [Cycle.ComponentSingularGe.cycleComponentSingularClosedFiltration_length]
  exact Set.image_empty _

/-- Every closed remainder stays below the singular-boundary dimension bound. -/
theorem Cycle.ComponentSingularGe.cycleComponentSingularClosedFiltration_dimension_lt
    {p : ℕ} (hx : Order.coheight x = p) (k : ℕ) :
    topologicalKrullDim (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k) < (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p : ℕ) :=
  (IsEmbedding.inclusion (Stratification.ClosedFiltration.reducedSmoothClosedFiltration_le _ _ k)).isInducing.topologicalKrullDim_le.trans_lt
    (AlgebraicGeometry.Smooth.SingularLocusDimension.topologicalKrullDim_cycleComponent_singularLocus_lt X x hx)

/-- Every smooth layer has strictly smaller dimension than the component. -/
theorem Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum_dimension_lt
    {p : ℕ} (hx : Order.coheight x = p) (k : ℕ) :
    topologicalKrullDim (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum X x k) < (Topology.Dimension.Basic.TopologicalSpace.dim X.left - p : ℕ) :=
  (AlgebraicGeometry.Smooth.SingularLocusDimension.topologicalKrullDim_reducedClosedSmoothPiece_le _ le_rfl).trans_lt
    (Cycle.ComponentSingularGe.cycleComponentSingularClosedFiltration_dimension_lt X x hx k)

/-- The normal codimension lower bound is realized on standard-smooth affine
neighborhoods of every stratum point, including strata of nonconstant dimension. -/
theorem Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge
    {p : ℕ} (hx : Order.coheight x = p) (k : ℕ)
    (z : Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum X x k) :
    ∃ (U : (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < Topology.Dimension.Basic.TopologicalSpace.dim X.left - p ∧ p + 1 ≤ Topology.Dimension.Basic.TopologicalSpace.dim X.left - n ∧
        RingHom.IsStandardSmoothOfRelativeDimension n
          ((Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k ≫ X.hom).appLE ⊤ U (by simp)).hom := by
  obtain ⟨U, hU, hzU, n, hn, hstd⟩ :=
    AlgebraicGeometry.Smooth.SingularLocusDimension.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k ≫ X.hom)
      (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum_dimension_lt X x hx k) z
  exact ⟨U, hU, hzU, n, hn, by omega, hstd⟩

/-- The dimension bound supplies smooth scheme morphisms of fixed local
dimension, ready for the normal-coordinate construction. -/
theorem Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum_exists_smooth_relativeDimension
    {p : ℕ} (hx : Order.coheight x = p) (k : ℕ)
    (z : Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum X x k) :
    ∃ (U : (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum X x k).Opens) (_ : IsAffineOpen U),
      z ∈ U ∧ ∃ n : ℕ, n < Topology.Dimension.Basic.TopologicalSpace.dim X.left - p ∧ p + 1 ≤ Topology.Dimension.Basic.TopologicalSpace.dim X.left - n ∧
        SmoothOfRelativeDimension n (U.ι ≫ Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k ≫ X.hom) := by
  obtain ⟨U, hU, hzU, n, hn, hcodim, hstd⟩ :=
    Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratum_exists_affine_normalCodimension_ge X x
      hx k z
  exact ⟨U, hU, hzU, n, hn, hcodim,
    AlgebraicGeometry.Smooth.AffineRelativeDimension.smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ hU hstd⟩

omit [IsIntegral X.left] [Smooth X.hom] in
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_antitone :
    Antitone (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x) :=
  fun _ _ hkl _ hz ↦ Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_antitone X x hkl hz

theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_length :
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x
      (AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length = ⊥ := by
  apply SetLike.coe_injective
  change ComplexPoint.Basic.Point.underlying ⁻¹'
    (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x
      (AlgebraicGeometry.Smooth.SingularLocusDimension.cycleComponentSingularStratification X x).length : Set X.left) = ∅
  rw [Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_length]
  exact Set.preimage_empty

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Each analytic successive difference is the complex-point image of its smooth stratum. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration_layer (k : ℕ) :
    Set.range (ComplexPoint.Basic.Point.map (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumOverι X x k)) =
      (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint.Basic.ComplexSchemePoint X)) \
        (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x (k + 1) : Set (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion X]
  change ComplexPoint.Basic.Point.underlying ⁻¹' Set.range (Cycle.ComponentSingularGe.cycleComponentSingularFiltrationStratumι X x k) = _
  rw [Cycle.ComponentSingularGe.cycleComponentSingularAmbientClosedFiltration_layer]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Inside the localization open, the stratum's closed-embedding image is the current analytic
closed support restricted to that open. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularStratumClosedLift_complexPoints_range (k : ℕ) :
    Set.range (ComplexPoint.Basic.Point.map (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLiftOver X x k)) =
      ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpen X x k)) ⁻¹'
          (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration X x k : Set (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion]
  change (ComplexPoint.Basic.Point.underlying : ComplexPoint.Basic.ComplexSchemePoint (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver X x k) →
    (Cycle.ComponentSingularGe.cycleComponentSingularStratumAmbientOpenOver X x k).left) ⁻¹'
      Set.range (Cycle.ComponentSingularGe.cycleComponentSingularStratumClosedLift X x k) = _
  rw [Cycle.ComponentSingularGe.range_cycleComponentSingularStratumClosedLift]
  rfl

end

end OAI.AlgebraicGeometry
