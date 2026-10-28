import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomotopy
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality

/-! # Relative Cup Presheaf -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupPresheaf.Constructions

noncomputable section

/-! A global relative two-cocycle gives a coherent cup map on all open sets. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (C : Set X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) 2)

def relativeTwoCocycleOpenRestriction (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U)) 2 :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (Opens.inclusion' U) (fun _ hx => hx)) 2 a

theorem relativeTwoCocycleOpenRestriction_naturality {U W : Opens X} (i : U ⟶ W) :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X C).map i.op) 2
        (relativeTwoCocycleOpenRestriction X C a W) =
      relativeTwoCocycleOpenRestriction X C a U := by
  unfold relativeTwoCocycleOpenRestriction
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp (ModuleCat.of ℚ ℚ)
    ((Opens.toTopCat X).map i) (Opens.inclusion' W)
    (A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U) (B := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W) (C := C)
    (fun _ hx => hx) (fun _ hx => hx)
  exact congrArg (fun f => AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap f 2 a) h

def relativeTwoCupOpenCochainMap (U : Opens X) :=
  RelativeCupHomotopy.Constructions.relativeTwoCupCochainMap (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U)
    (relativeTwoCocycleOpenRestriction X C a U)

theorem relativeTwoCupOpenCochainMap_naturality {U W : Opens X} (i : U ⟶ W) :
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainPresheaf (ModuleCat.of ℚ ℚ) X).map i.op ≫
        relativeTwoCupOpenCochainMap X C a U =
      relativeTwoCupOpenCochainMap X C a W ≫
        HomologicalComplex.restrictionMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X C).map i.op)
          (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) := by
  have h := RelativeCupHomotopy.Constructions.relativeTwoCupCochainMap_naturality (TopCat.of W) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W)
    (relativeTwoCocycleOpenRestriction X C a W) ((Opens.toTopCat X).map i)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U) (fun _ hx => hx)
  change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback _ _ ≫ RelativeCupHomotopy.Constructions.relativeTwoCupCochainMap _ _
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X C).map i.op) 2
      (relativeTwoCocycleOpenRestriction X C a W)) = _ at h
  rw [relativeTwoCocycleOpenRestriction_naturality] at h
  exact h

def relativeTwoCupPresheafComplexMap :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X C).restriction (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2) where
  f n :=
    { app U := (relativeTwoCupOpenCochainMap X C a U.unop).f n
      naturality U W i := congrArg (fun f => f.f n)
        (relativeTwoCupOpenCochainMap_naturality X C a i.unop) }
  comm' i j hij := by
    apply NatTrans.ext
    funext U
    exact (relativeTwoCupOpenCochainMap X C a U.unop).comm' i j hij

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupPresheaf.Constructions
