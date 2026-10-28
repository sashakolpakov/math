import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Cohomology.Singular.Coefficients
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Topology.Sets.Compacts

/-! # Compact Support Cohomology -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCohomology

noncomputable section

/-!
# Compactly supported singular cochains

For a compact subset `K` of an actual topological space `X`, the support stage
is the relative singular cochain complex `C*(X, X \ K; M)`. Its inclusion into
ordinary cochains is the kernel of restriction to the complement of `K`.
Inclusions of compact sets give the usual inclusions of these kernels. The
filtered colimit over all compact subsets defines compactly supported
singular cochains, and its actual cohomology defines compactly supported
singular cohomology.

On a compact space the largest support is terminal. The resulting comparison
with ordinary cochains is an isomorphism, proved below without a duality
hypothesis or a choice of support theory.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {R : Type} [Ring R]

/-- The genuine relative cochain complex for the complement of a compact set. -/
abbrev compactSupportCochainStage (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) : CochainComplex (ModuleCat.{0} R) ℕ :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochains M X (K : Set X)ᶜ

/-- A cochain with support in `K` is an ordinary cochain vanishing on `X \ K`. -/
abbrev compactSupportCochainStageInclusion (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) : compactSupportCochainStage M X K ⟶ Cohomology.Singular.Basic.singularCochains M X :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X (K : Set X)ᶜ

/-- The degreewise support condition is exactly the kernel of restriction. -/
theorem compactSupportCochainStage_range (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) (n : ℕ) :
    LinearMap.range ((compactSupportCochainStageInclusion M X K).f n).hom =
      LinearMap.ker ((Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X (K : Set X)ᶜ).f n).hom :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range M X (K : Set X)ᶜ n

/-- Enlarging a compact support gives the actual map of relative kernels. -/
def compactSupportCochainMap (M : ModuleCat.{0} R) {X : TopCat.{0}}
    {K L : Compacts X} (h : K ≤ L) :
    compactSupportCochainStage M X K ⟶ compactSupportCochainStage M X L :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (𝟙 X) (by
    intro x hx hxK
    exact hx (h hxK))

@[reassoc (attr := simp)]
theorem compactSupportCochainMap_inclusion (M : ModuleCat.{0} R)
    {X : TopCat.{0}} {K L : Compacts X} (h : K ≤ L) :
    compactSupportCochainMap M h ≫ compactSupportCochainStageInclusion M X L =
      compactSupportCochainStageInclusion M X K := by
  simpa only [compactSupportCochainMap, Cohomology.Singular.Functor.singularPullback_id, Category.comp_id] using
    Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M (𝟙 X)
      (show Set.MapsTo (𝟙 X) (L : Set X)ᶜ (K : Set X)ᶜ from
        fun _ hx hxK => hx (h hxK))

/-- All transition maps are monomorphisms of actual cochain complexes. -/
instance compactSupportCochainMap_mono (M : ModuleCat.{0} R)
    {X : TopCat.{0}} {K L : Compacts X} (h : K ≤ L) :
    Mono (compactSupportCochainMap M h) :=
  mono_of_mono_fac (compactSupportCochainMap_inclusion M h)

@[simp]
theorem compactSupportCochainMap_refl (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) : compactSupportCochainMap M (le_refl K) = 𝟙 _ := by
  apply (cancel_mono (compactSupportCochainStageInclusion M X K)).1
  simp

@[simp]
theorem compactSupportCochainMap_comp (M : ModuleCat.{0} R)
    {X : TopCat.{0}} {K L N : Compacts X} (h : K ≤ L) (h' : L ≤ N) :
    compactSupportCochainMap M h ≫ compactSupportCochainMap M h' =
      compactSupportCochainMap M (h.trans h') := by
  apply (cancel_mono (compactSupportCochainStageInclusion M X N)).1
  simp

/-- The indexing category is filtered because finite unions of compact sets
are compact, and the empty set is a compact set. -/
theorem compactSupports_isFiltered (X : TopCat.{0}) : IsFiltered (Compacts X) :=
  inferInstance

/-- The directed system of the actual support-relative cochain complexes. -/
def compactSupportCochainDiagram (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Compacts X ⥤ CochainComplex (ModuleCat.{0} R) ℕ where
  obj K := compactSupportCochainStage M X K
  map f := compactSupportCochainMap M (leOfHom f)
  map_id K := compactSupportCochainMap_refl M X K
  map_comp f g := (compactSupportCochainMap_comp M (leOfHom f) (leOfHom g)).symm

/-- The ordinary cochain inclusions form a genuine cocone on the support system. -/
def compactSupportCochainCocone (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Cocone (compactSupportCochainDiagram M X) where
  pt := Cohomology.Singular.Basic.singularCochains M X
  ι := {
    app := fun K => compactSupportCochainStageInclusion M X K
    naturality := fun _ _ f => by
      change compactSupportCochainMap M (leOfHom f) ≫ _ = _ ≫ 𝟙 _
      rw [Category.comp_id, compactSupportCochainMap_inclusion] }

/-- Compactly supported singular cochains are the colimit over compact supports. -/
abbrev compactSupportedCochains (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  colimit (compactSupportCochainDiagram M X)

/-- Place a relative cochain with compact support in the colimit complex. -/
abbrev compactSupportCochainι (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) : compactSupportCochainStage M X K ⟶ compactSupportedCochains M X :=
  colimit.ι (compactSupportCochainDiagram M X) K

@[reassoc (attr := simp)]
theorem compactSupportCochainMap_ι (M : ModuleCat.{0} R)
    {X : TopCat.{0}} {K L : Compacts X} (h : K ≤ L) :
    compactSupportCochainMap M h ≫ compactSupportCochainι M X L =
      compactSupportCochainι M X K :=
  colimit.w (compactSupportCochainDiagram M X) (homOfLE h)

/-- Forget compact support using the actual cocone of kernel inclusions. -/
def compactSupportedCochainForget (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    compactSupportedCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X :=
  colimit.desc (compactSupportCochainDiagram M X) (compactSupportCochainCocone M X)

@[reassoc (attr := simp)]
theorem compactSupportCochainι_forget (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) :
    compactSupportCochainι M X K ≫ compactSupportedCochainForget M X =
      compactSupportCochainStageInclusion M X K :=
  colimit.ι_desc (compactSupportCochainCocone M X) K

/-- Compactly supported cohomology is the cohomology of this actual complex. -/
abbrev compactSupportedCohomology (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    ModuleCat.{0} R := (compactSupportedCochains M X).homology n

/-- The support-relative cohomology groups with their induced transition maps. -/
def compactSupportCohomologyDiagram (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    Compacts X ⥤ ModuleCat.{0} R :=
  compactSupportCochainDiagram M X ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n

/-- The map from a compact support's relative cohomology to compact support cohomology. -/
abbrev compactSupportCohomologyι (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (K : Set X)ᶜ n ⟶ compactSupportedCohomology M X n :=
  HomologicalComplex.homologyMap (compactSupportCochainι M X K) n

/-- Forgetting support on actual singular cohomology. -/
abbrev compactSupportedCohomologyForget (M : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    compactSupportedCohomology M X n ⟶ Cohomology.Singular.Basic.singularCohomology M X n :=
  HomologicalComplex.homologyMap (compactSupportedCochainForget M X) n

@[reassoc (attr := simp)]
theorem compactSupportCohomologyι_forget (M : ModuleCat.{0} R) (X : TopCat.{0})
    (K : Compacts X) (n : ℕ) :
    compactSupportCohomologyι M X K n ≫ compactSupportedCohomologyForget M X n =
      Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X (K : Set X)ᶜ n := by
  rw [← HomologicalComplex.homologyMap_comp, compactSupportCochainι_forget]

/-- An empty topological space has the zero complex of singular cochains. -/
theorem singularCochains_isZero_of_isEmpty (M : ModuleCat.{0} R)
    (X : TopCat.{0}) [IsEmpty X] : IsZero (Cohomology.Singular.Basic.singularCochains M X) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.hom_ext
  intro n
  have : IsEmpty (Cohomology.Singular.Basic.singularSimplices X n) := ⟨fun s =>
    isEmptyElim (Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n s
      (Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 1))))⟩
  exact ((ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R (Cohomology.Singular.Basic.singularSimplices X n → M))).of_iso
      (Cohomology.Singular.Coefficients.singularDegreewiseFunctionIso M X n)).eq_of_tgt _ _

/-- Restriction to an empty subspace is the zero map of cochain complexes. -/
theorem subspaceCochainRestriction_eq_zero_of_isEmpty (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) [IsEmpty A] :
    Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A = 0 :=
  (singularCochains_isZero_of_isEmpty M (TopCat.of A)).eq_of_tgt _ _

variable (M : ModuleCat.{0} R) (X : TopCat.{0}) [CompactSpace X]

/-- At the largest compact support, the relative kernel is all ordinary cochains. -/
def compactSupportTopCochainIso :
    compactSupportCochainStage M X ⊤ ≅ Cohomology.Singular.Basic.singularCochains M X where
  hom := compactSupportCochainStageInclusion M X ⊤
  inv := kernel.lift (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X (↑(⊤ : Compacts X) : Set X)ᶜ)
    (𝟙 _) (by
      have : IsEmpty ↥((↑(⊤ : Compacts X) : Set X)ᶜ) :=
        ⟨fun x => x.property (by simp)⟩
      rw [subspaceCochainRestriction_eq_zero_of_isEmpty, comp_zero])
  hom_inv_id := by
    apply (cancel_mono (compactSupportCochainStageInclusion M X ⊤)).1
    simp
  inv_hom_id := by simp

@[simp]
theorem compactSupportTopCochainIso_hom :
    (compactSupportTopCochainIso M X).hom = compactSupportCochainStageInclusion M X ⊤ := rfl

/-- The largest support is terminal, so its colimit insertion is an isomorphism. -/
instance compactSupportCochainι_top_isIso : IsIso (compactSupportCochainι M X ⊤) :=
  isIso_ι_of_isTerminal isTerminalTop (compactSupportCochainDiagram M X)

/-- On a compact space, forgetting compact support is an isomorphism of complexes. -/
instance compactSupportedCochainForget_isIso : IsIso (compactSupportedCochainForget M X) := by
  have : IsIso (compactSupportCochainStageInclusion M X ⊤) :=
    (compactSupportTopCochainIso M X).isIso_hom
  have : IsIso (compactSupportCochainι M X ⊤ ≫ compactSupportedCochainForget M X) := by
    rw [compactSupportCochainι_forget]
    infer_instance
  exact IsIso.of_isIso_comp_left (compactSupportCochainι M X ⊤)
    (compactSupportedCochainForget M X)

/-- The canonical ordinary/compact support comparison on a compact space. -/
def compactSupportedCochainIso : compactSupportedCochains M X ≅ Cohomology.Singular.Basic.singularCochains M X :=
  asIso (compactSupportedCochainForget M X)

@[simp]
theorem compactSupportedCochainIso_hom :
    (compactSupportedCochainIso M X).hom = compactSupportedCochainForget M X := rfl

/-- Compact support cohomology equals ordinary singular cohomology on compact spaces. -/
def compactSupportedCohomologyIso (n : ℕ) :
    compactSupportedCohomology M X n ≅ Cohomology.Singular.Basic.singularCohomology M X n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) n).mapIso
    (compactSupportedCochainIso M X)

@[simp]
theorem compactSupportedCohomologyIso_hom (n : ℕ) :
    (compactSupportedCohomologyIso M X n).hom = compactSupportedCohomologyForget M X n := rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportCohomology
