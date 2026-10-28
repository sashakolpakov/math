import OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupComplex
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality

/-! # Even Cup Presheaf -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupPresheaf.Constructions

noncomputable section

/-! A global relative even-degree cocycle gives a coherent cup map on all open sets. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) (C : Set X)
variable {p : ℕ}
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X C) (2 * p))

def relativeEvenCocycleOpenRestriction (U : Opens X) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U)) (2 * p) :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (Opens.inclusion' U) (fun _ hx => hx)) (2 * p) a

theorem relativeEvenCocycleOpenRestriction_naturality {U W : Opens X} (i : U ⟶ W) :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X C).map i.op) (2 * p)
        (relativeEvenCocycleOpenRestriction X C a W) =
      relativeEvenCocycleOpenRestriction X C a U := by
  unfold relativeEvenCocycleOpenRestriction
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp (ModuleCat.of ℚ ℚ)
    ((Opens.toTopCat X).map i) (Opens.inclusion' W)
    (A := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U) (B := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W) (C := C)
    (fun _ hx => hx) (fun _ hx => hx)
  exact congrArg (fun f => AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap f (2 * p) a) h

def relativeEvenCupOpenCochainMap (U : Opens X) :=
  EvenCupComplex.Constructions.relativeEvenCupCochainMap (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U)
    (relativeEvenCocycleOpenRestriction X C a U)

theorem relativeEvenCupOpenCochainMap_naturality {U W : Opens X} (i : U ⟶ W) :
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainPresheaf (ModuleCat.of ℚ ℚ) X).map i.op ≫
        relativeEvenCupOpenCochainMap X C a U =
      relativeEvenCupOpenCochainMap X C a W ≫
        HomologicalComplex.restrictionMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X C).map i.op)
          (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) := by
  have h := EvenCupComplex.Constructions.relativeEvenCupCochainMap_naturality (TopCat.of W) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C W)
    (relativeEvenCocycleOpenRestriction X C a W) ((Opens.toTopCat X).map i)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace C U) (fun _ hx => hx)
  change AlgebraicTopology.Cohomology.Singular.Functor.singularPullback _ _ ≫ EvenCupComplex.Constructions.relativeEvenCupCochainMap _ _
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X C).map i.op) (2 * p)
      (relativeEvenCocycleOpenRestriction X C a W)) = _ at h
  rw [relativeEvenCocycleOpenRestriction_naturality] at h
  exact h

def relativeEvenCupPresheafComplexMap :
    AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X ⟶
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativePresheafComplex (ModuleCat.of ℚ ℚ) X C).restriction (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2 * p)) where
  f n :=
    { app U := (relativeEvenCupOpenCochainMap X C a U.unop).f n
      naturality U W i := congrArg (fun f => f.f n)
        (relativeEvenCupOpenCochainMap_naturality X C a i.unop) }
  comm' i j hij := by
    apply NatTrans.ext
    funext U
    exact (relativeEvenCupOpenCochainMap X C a U.unop).comm' i j hij

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupPresheaf.Constructions
