import OAI.AlgebraicTopology.Cohomology.Singular.Functor
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Relative Sequence -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence

noncomputable section

/-!
# Relative singular cohomology and the long exact sequence of a pair

For a topological space `X` and a subspace `A`, relative cochains are the
kernel of restriction `C*(X; M) → C*(A; M)`. Restriction is degreewise
surjective: the singular chain functor in the opposite module category
preserves the monomorphism of the subspace inclusion. The resulting genuine
short exact sequence gives the connecting homomorphism and the long exact
sequence in cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {R : Type} [Ring R]

/-- Pullback along an injective continuous map is surjective on cochains.
This is the opposite-category form of extending arbitrary functions from
an injectively included set of singular simplices. -/
instance singularPullback_epi (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) [Mono f] : Epi (Functor.singularPullback M f) := by
  change Epi ((HomologicalComplex.unopFunctor (ModuleCat.{0} R)
    (ComplexShape.down ℕ)).map
      ((((AlgebraicTopology.singularChainComplexFunctor
        ((ModuleCat.{0} R)ᵒᵖ)).obj (op M)).map f).op))
  infer_instance

/-- Restrict ordinary singular cochains to a subspace. -/
abbrev subspaceCochainRestriction (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    Basic.singularCochains M X ⟶ Basic.singularCochains M (TopCat.of A) :=
  Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)

/-- Restriction to a subspace is surjective in every cochain degree. -/
instance subspaceCochainRestriction_f_epi (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Epi ((subspaceCochainRestriction M X A).f n) := by
  infer_instance

/-- Relative singular cochains consist of cochains vanishing on the subspace. -/
abbrev relativeSingularCochains (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  kernel (subspaceCochainRestriction M X A)

/-- Include relative cochains into absolute cochains. -/
abbrev relativeCochainInclusion (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    relativeSingularCochains M X A ⟶ Basic.singularCochains M X :=
  kernel.ι (subspaceCochainRestriction M X A)

@[reassoc (attr := simp)]
theorem relativeCochainInclusion_restriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) :
    relativeCochainInclusion M X A ≫ subspaceCochainRestriction M X A = 0 :=
  kernel.condition _

/-- The actual singular-cochain sequence of a pair. -/
def relativeCochainSequence (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ) :=
  ShortComplex.mk (relativeCochainInclusion M X A) (subspaceCochainRestriction M X A)
    (relativeCochainInclusion_restriction M X A)

/-- `0 → C*(X,A;M) → C*(X;M) → C*(A;M) → 0` is short exact. -/
theorem relativeCochainSequence_shortExact (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) :
    (relativeCochainSequence M X A).ShortExact := by
  change (ShortComplex.mk (kernel.ι (subspaceCochainRestriction M X A))
    (subspaceCochainRestriction M X A) _).ShortExact
  exact { exact := ShortComplex.kernelSequence_exact (subspaceCochainRestriction M X A) }

/-- The relative-cochain sequence is short exact in every degree. -/
theorem relativeCochainSequence_degreewiseShortExact (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ((relativeCochainSequence M X A).map
      (HomologicalComplex.eval (ModuleCat.{0} R) (ComplexShape.up ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (relativeCochainSequence_shortExact M X A) n

/-- In every degree, relative cochains have exactly the kernel of restriction
as their image in the ordinary singular cochains. -/
theorem relativeCochainInclusion_range (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range ((relativeCochainInclusion M X A).f n).hom =
      LinearMap.ker ((subspaceCochainRestriction M X A).f n).hom :=
  (relativeCochainSequence_degreewiseShortExact M X A n).exact.moduleCat_range_eq_ker

/-- Relative singular cohomology of an actual pair of topological spaces. -/
abbrev relativeSingularCohomology (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) : ModuleCat.{0} R :=
  (relativeSingularCochains M X A).homology n

/-- The forgetful map from relative to absolute cohomology. -/
abbrev relativeCohomologyInclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeSingularCohomology M X A n ⟶ Basic.singularCohomology M X n :=
  HomologicalComplex.homologyMap (relativeCochainInclusion M X A) n

/-- Restriction from absolute cohomology to the cohomology of a subspace. -/
abbrev subspaceCohomologyRestriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Basic.singularCohomology M X n ⟶ Basic.singularCohomology M (TopCat.of A) n :=
  Functor.singularCohomologyPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) n

/-- The connecting map `H^n(A;M) → H^(n+1)(X,A;M)` of a pair. -/
def relativeCohomologyConnecting (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Basic.singularCohomology M (TopCat.of A) n ⟶ relativeSingularCohomology M X A (n + 1) :=
  (relativeCochainSequence_shortExact M X A).δ n (n + 1) rfl

@[reassoc (attr := simp)]
theorem relativeCohomologyInclusion_restriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeCohomologyInclusion M X A n ≫ subspaceCohomologyRestriction M X A n = 0 := by
  change HomologicalComplex.homologyMap (relativeCochainInclusion M X A) n ≫
    HomologicalComplex.homologyMap (subspaceCochainRestriction M X A) n = 0
  rw [← HomologicalComplex.homologyMap_comp, relativeCochainInclusion_restriction,
    HomologicalComplex.homologyMap_zero]

@[reassoc (attr := simp)]
theorem subspaceCohomologyRestriction_connecting (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    subspaceCohomologyRestriction M X A n ≫ relativeCohomologyConnecting M X A n = 0 :=
  (relativeCochainSequence_shortExact M X A).comp_δ n (n + 1) rfl

@[reassoc (attr := simp)]
theorem relativeCohomologyConnecting_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeCohomologyConnecting M X A n ≫ relativeCohomologyInclusion M X A (n + 1) = 0 :=
  (relativeCochainSequence_shortExact M X A).δ_comp n (n + 1) rfl

/-- Exactness at `H^n(X;M)` in the long exact sequence of a pair. -/
theorem relativeCohomology_exact_absolute (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relativeCohomologyInclusion M X A n)
      (subspaceCohomologyRestriction M X A n)
      (relativeCohomologyInclusion_restriction M X A n)).Exact :=
  (relativeCochainSequence_shortExact M X A).homology_exact₂ n

/-- Exactness at `H^n(A;M)` in the long exact sequence of a pair. -/
theorem relativeCohomology_exact_subspace (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (subspaceCohomologyRestriction M X A n)
      (relativeCohomologyConnecting M X A n)
      (subspaceCohomologyRestriction_connecting M X A n)).Exact :=
  (relativeCochainSequence_shortExact M X A).homology_exact₃ n (n + 1) rfl

/-- Exactness at `H^(n+1)(X,A;M)` in the long exact sequence of a pair. -/
theorem relativeCohomology_exact_relative (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relativeCohomologyConnecting M X A n)
      (relativeCohomologyInclusion M X A (n + 1))
      (relativeCohomologyConnecting_inclusion M X A n)).Exact :=
  (relativeCochainSequence_shortExact M X A).homology_exact₁ n (n + 1) rfl

/-- An absolute class has a relative lift exactly when its restriction vanishes. -/
theorem relativeCohomology_range_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (relativeCohomologyInclusion M X A n).hom =
      LinearMap.ker (subspaceCohomologyRestriction M X A n).hom :=
  (relativeCohomology_exact_absolute M X A n).moduleCat_range_eq_ker

/-- A subspace class extends to the ambient space exactly when its connecting
class vanishes. -/
theorem relativeCohomology_range_restriction (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (subspaceCohomologyRestriction M X A n).hom =
      LinearMap.ker (relativeCohomologyConnecting M X A n).hom :=
  (relativeCohomology_exact_subspace M X A n).moduleCat_range_eq_ker

/-- A positive-degree relative class is a connecting class exactly when its
ambient class vanishes. -/
theorem relativeCohomology_range_connecting (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (relativeCohomologyConnecting M X A n).hom =
      LinearMap.ker (relativeCohomologyInclusion M X A (n + 1)).hom :=
  (relativeCohomology_exact_relative M X A n).moduleCat_range_eq_ker

/-- The long exact sequence starts injectively in degree zero. -/
instance relativeCohomologyInclusion_zero_mono (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) :
    Mono (relativeCohomologyInclusion M X A 0) := by
  apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
  intro i hi
  exact Nat.succ_ne_zero i hi

/-- A continuous map of pairs pulls relative singular cochains back. -/
def relativeSingularCochainsMap (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    relativeSingularCochains M Y B ⟶ relativeSingularCochains M X A :=
  kernel.map (subspaceCochainRestriction M Y B) (subspaceCochainRestriction M X A)
    (Functor.singularPullback M f) (Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h)) (by
      change Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B) ≫
          Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h) =
        Functor.singularPullback M f ≫ Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)
      rw [← Functor.singularPullback_comp, ← Functor.singularPullback_comp, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap_inclusion])

@[reassoc (attr := simp)]
theorem relativeCochainInclusion_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    relativeSingularCochainsMap M f h ≫ relativeCochainInclusion M X A =
      relativeCochainInclusion M Y B ≫ Functor.singularPullback M f :=
  kernel.lift_ι _ _ _

/-- A continuous map of pairs pulls relative cohomology classes back. -/
abbrev relativeSingularCohomologyMap (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) :
    relativeSingularCohomology M Y B n ⟶ relativeSingularCohomology M X A n :=
  HomologicalComplex.homologyMap (relativeSingularCochainsMap M f h) n

/-- A map of pairs gives a morphism of the actual short exact cochain sequences. -/
def relativeCochainSequenceMap (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) :
    relativeCochainSequence M Y B ⟶ relativeCochainSequence M X A where
  τ₁ := relativeSingularCochainsMap M f h
  τ₂ := Functor.singularPullback M f
  τ₃ := Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h)
  comm₁₂ := relativeCochainInclusion_naturality M f h
  comm₂₃ := by
    change Functor.singularPullback M f ≫ Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) =
      Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B) ≫
        Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h)
    rw [← Functor.singularPullback_comp, ← Functor.singularPullback_comp, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap_inclusion]

/-- The connecting maps commute with pullback along continuous maps of pairs. -/
@[reassoc]
theorem relativeCohomologyConnecting_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A : Set X} {B : Set Y}
    (h : Set.MapsTo f A B) (n : ℕ) :
    relativeCohomologyConnecting M Y B n ≫ relativeSingularCohomologyMap M f h (n + 1) =
      Functor.singularCohomologyPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap f h) n ≫
        relativeCohomologyConnecting M X A n :=
  HomologicalComplex.HomologySequence.δ_naturality (relativeCochainSequenceMap M f h)
    (relativeCochainSequence_shortExact M Y B) (relativeCochainSequence_shortExact M X A)
    n (n + 1) rfl

/-- If adjacent ambient cohomology groups vanish, the connecting map is an
isomorphism from subspace to relative cohomology. -/
def relativeCohomologyConnectingIso (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (hi : IsZero (Basic.singularCohomology M X n))
    (hj : IsZero (Basic.singularCohomology M X (n + 1))) :
    Basic.singularCohomology M (TopCat.of A) n ≅ relativeSingularCohomology M X A (n + 1) :=
  (relativeCochainSequence_shortExact M X A).δIso n (n + 1) rfl hi hj

@[simp]
theorem relativeCohomologyConnectingIso_hom (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (hi : IsZero (Basic.singularCohomology M X n))
    (hj : IsZero (Basic.singularCohomology M X (n + 1))) :
    (relativeCohomologyConnectingIso M X A n hi hj).hom =
      relativeCohomologyConnecting M X A n := rfl

end

end OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
