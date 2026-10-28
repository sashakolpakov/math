import OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestrictionBetween
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality
import OAI.AlgebraicTopology.Cohomology.Singular.PullbackHomotopyNaturality

/-! # Relative Cochain Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology

noncomputable section

/-!
# Actual homotopies on relative singular cochains

A continuous homotopy preserving a pair restricts to an actual homotopy on
the two subspaces. Naturality of the singular prism homotopy then preserves
the kernel of cochain restriction. Restriction through that kernel gives an
actual relative cochain homotopy, and hence pair homotopy invariance.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

/-- The genuine relative cochain inclusion is injective in every degree. -/
theorem relativeCochainInclusion_injective (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Function.Injective ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The actual singular cochain homotopy preserves the relative kernel.
Its restriction to the subspace is the corresponding actual prism homotopy. -/
theorem singularPullbackHomotopy_preserves_relative (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B)
    (a b : ℕ) (c : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y B).X a) :
    (AlgebraicTopology.Cohomology.Singular.Homotopy.singularPullbackHomotopy M H).hom a b ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f a c) ∈
      LinearMap.range ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f b).hom := by
  rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_range]
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f b
    ((AlgebraicTopology.Cohomology.Singular.Homotopy.singularPullbackHomotopy M H).hom a b ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f a c)) = 0
  have hz : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M Y B).f a
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f a c) = 0 :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_restriction M Y B) a) c
  have hnat := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.PullbackHomotopyNaturality.singularPullbackHomotopy_subspace_naturality M hf hg H hH a b)
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f a c)
  change (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X A).f b
      ((AlgebraicTopology.Cohomology.Singular.Homotopy.singularPullbackHomotopy M H).hom a b ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f a c)) =
    (AlgebraicTopology.Cohomology.Singular.Homotopy.singularPullbackHomotopy M (RelativeHomotopy.Cycles.subspaceHomotopy hf hg H hH)).hom a b
      ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M Y B).f a ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f a c)) at hnat
  rw [hnat, hz, map_zero]

/-- A genuine continuous homotopy of pairs induces an actual homotopy
between their relative singular-cochain pullbacks. -/
def relativeSingularCochainsHomotopy (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) :
    Homotopy (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f hf) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M g hg) :=
  InjectiveHomotopyRestrictionBetween.Cycles.restrictHomotopyBetween (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A)
    (relativeCochainInclusion_injective M X A)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M f hf) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M g hg)
    (AlgebraicTopology.Cohomology.Singular.Homotopy.singularPullbackHomotopy M H)
    (singularPullbackHomotopy_preserves_relative M hf hg H hH)

/-- The relative homotopy components recover the actual ambient cochain
homotopy after inclusion, rather than merely an abstract homotopy class. -/
@[reassoc]
theorem relativeSingularCochainsHomotopy_inclusion (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (a b : ℕ) :
    (relativeSingularCochainsHomotopy M hf hg H hH).hom a b ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f b =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion M Y B).f a ≫ (AlgebraicTopology.Cohomology.Singular.Homotopy.singularPullbackHomotopy M H).hom a b :=
  InjectiveHomotopyRestrictionBetween.Cycles.restrictedBetweenComponent_comp _ _ _ _ _ a b

/-- Pair-homotopic maps induce equal pullbacks on relative singular cohomology. -/
theorem relativeSingularCohomologyMap_eq_of_homotopy (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {f g : X ⟶ Y} {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g)
    (hH : ∀ t : unitInterval, Set.MapsTo (fun x => H (t, x)) A B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hf n = AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M g hg n :=
  (relativeSingularCochainsHomotopy M hf hg H hH).homologyMap_eq n

/-- An explicit homotopy equivalence of pairs induces a contravariant
homotopy equivalence of their actual relative singular-cochain complexes. -/
def relativeSingularCochainsHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (g : Y ⟶ X) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B A)
    (HX : TopCat.Homotopy (f ≫ g) (𝟙 X)) (HY : TopCat.Homotopy (g ≫ f) (𝟙 Y))
    (hHX : ∀ t : unitInterval, Set.MapsTo (fun x => HX (t, x)) A A)
    (hHY : ∀ t : unitInterval, Set.MapsTo (fun y => HY (t, y)) B B) :
    HomotopyEquiv (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M Y B) (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) where
  hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f hf
  inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M g hg
  homotopyHomInvId := by
    have h := relativeSingularCochainsHomotopy M
      (X := Y) (Y := Y) (f := g ≫ f) (g := 𝟙 Y) (A := B) (B := B)
      (fun _ hy => hf (hg hy)) (fun _ hy => hy) HY hHY
    simpa only [RelativeCochainFunctoriality.Cohomology.relativeSingularCochainsMap_of_comp M g f hg hf,
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_id] using! h
  homotopyInvHomId := by
    have h := relativeSingularCochainsHomotopy M
      (X := X) (Y := X) (f := f ≫ g) (g := 𝟙 X) (A := A) (B := A)
      (fun _ hx => hg (hf hx)) (fun _ hx => hx) HX hHX
    simpa only [RelativeCochainFunctoriality.Cohomology.relativeSingularCochainsMap_of_comp M f g hf hg,
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_id] using! h

/-- The corresponding isomorphism on genuine relative cohomology, with
the pair maps and pair-preserving homotopies supplied explicitly. -/
def relativeSingularCohomologyIsoOfPairHomotopyEquiv (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (g : Y ⟶ X) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B A)
    (HX : TopCat.Homotopy (f ≫ g) (𝟙 X)) (HY : TopCat.Homotopy (g ≫ f) (𝟙 Y))
    (hHX : ∀ t : unitInterval, Set.MapsTo (fun x => HX (t, x)) A A)
    (hHY : ∀ t : unitInterval, Set.MapsTo (fun y => HY (t, y)) B B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y B n ≅ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n :=
  (relativeSingularCochainsHomotopyEquiv M f g hf hg HX HY hHX hHY).toHomologyIso n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology
