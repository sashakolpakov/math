import OAI.AlgebraicTopology.Products.RelativeCochainEndomorphism
import OAI.AlgebraicTopology.Products.SingularReversalHomotopy

/-! # Relative Reversal -/

namespace OAI.AlgebraicTopology.Products.RelativeReversal

noncomputable section

/-!
# Signed vertex reversal on actual relative singular cochains

Naturality for the continuous inclusion of a subspace makes signed reversal
preserve the actual kernel of restriction. The same naturality for its proven
homotopy restricts that homotopy to the kernel, so relative cohomology sees the
identity. No stability claim for an arbitrary simplicial subcomplex is used.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R]

/-- Actual signed reversal, restricted to the genuine relative kernel. -/
def relativeReversalCochainMap (M : ModuleCat.{0} R) (X : TopCat.{0}) (A : Set X) :
    Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A ⟶ Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A :=
  RelativeCochainEndomorphism.relativeCochainEndomorphism M X A
    (SingularReversalHomotopy.singularReversalCochainMap M X) (SingularReversalHomotopy.singularReversalCochainMap M (TopCat.of A))
    (SingularReversalHomotopy.singularReversalCochainMap_naturality M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).symm

@[reassoc (attr := simp)]
theorem relativeReversalCochainMap_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) :
    relativeReversalCochainMap M X A ≫ Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A =
      Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A ≫ SingularReversalHomotopy.singularReversalCochainMap M X :=
  RelativeCochainEndomorphism.relativeCochainEndomorphism_inclusion M X A _ _ _

@[simp]
theorem relativeReversalCochainMap_inclusion_apply (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).X n) :
    (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n ((relativeReversalCochainMap M X A).f n c) =
      (SingularReversalHomotopy.singularReversalCochainMap M X).f n ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f n c) :=
  RelativeCochainEndomorphism.relativeCochainEndomorphism_inclusion_apply M X A _ _ _ n c

/-- The actual ambient reversal homotopy descends to the actual relative complex. -/
def relativeReversalCochainHomotopy (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) :
    Homotopy (relativeReversalCochainMap M X A) (𝟙 _) :=
  RelativeCochainEndomorphism.relativeCochainEndomorphismHomotopyId M X A
    (SingularReversalHomotopy.singularReversalCochainMap M X) (SingularReversalHomotopy.singularReversalCochainMap M (TopCat.of A))
    (SingularReversalHomotopy.singularReversalCochainMap_naturality M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).symm
    (SingularReversalHomotopy.singularReversalCochainHomotopy M X)
    (SingularReversalHomotopy.singularReversalCochainHomotopy M (TopCat.of A))
    (SingularReversalHomotopy.singularReversalCochainHomotopy_naturality M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A))

/-- Inclusion identifies the relative homotopy with the original ambient one. -/
@[reassoc]
theorem relativeReversalCochainHomotopy_inclusion (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (a b : ℕ) :
    (relativeReversalCochainHomotopy M X A).hom a b ≫
        (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f b =
      (Cohomology.Singular.RelativeSequence.relativeCochainInclusion M X A).f a ≫
        (SingularReversalHomotopy.singularReversalCochainHomotopy M X).hom a b :=
  RelativeCochainEndomorphism.relativeCochainEndomorphismHomotopyId_inclusion M X A _ _ _ _ _ _ a b

/-- Signed reversal induces identity on the relative cohomology of every pair. -/
@[simp]
theorem relativeReversalCochainMap_homologyMap (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeReversalCochainMap M X A) n =
      𝟙 ((Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A).homology n) := by
  simpa only [HomologicalComplex.homologyMap_id] using
    (relativeReversalCochainHomotopy M X A).homologyMap_eq n

/-- Every relative cocycle represents the same class as its signed reversal. -/
@[simp]
theorem relativeReversalCochainMap_class (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n) :
    Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n
      (Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (relativeReversalCochainMap M X A) n c) =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains M X A) n c := by
  rw [← Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, relativeReversalCochainMap_homologyMap]
  rfl

end

end OAI.AlgebraicTopology.Products.RelativeReversal
