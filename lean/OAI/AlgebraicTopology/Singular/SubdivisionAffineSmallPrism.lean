/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicTopology.Singular.SubdivisionAffinePrism
import OAI.AlgebraicTopology.Singular.SubdivisionAffineSmall
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Subdivision Affine Small Prism -/

namespace OAI.AlgebraicTopology.Singular.SubdivisionAffineSmallPrism

noncomputable section

/-!

# The affine subdivision prism on cover-small singular chains

The universal affine prism only precomposes a singular simplex. It therefore preserves the
range of any cover member, just as affine subdivision itself does. This file restricts the
prism to the cover-small chain complex and proves that cover-small affine subdivision is chain
homotopic to the identity there.
-/

open _root_.AlgebraicTopology _root_.CategoryTheory _root_.CategoryTheory.Limits Set

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- The affine prism on a selected lift of a cover-small generator, mapped back into the small
chain complex. -/
noncomputable def coverSmallAffinePrismSimplexChain
    (n : ℕ)
    (x : (ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    AddCommGrpCat.of ℤ ⟶
      (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X (n + 1) :=
  (TopCat.toSSet.obj
      (TopCat.of (U (SubdivisionAffineSmall.coverSmallSimplexPreimageIndex X U x)))).ιChainComplex
        (SubdivisionAffineSmall.coverSmallSimplexPreimage X U x) ≫
    SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent
      (TopCat.of (U (SubdivisionAffineSmall.coverSmallSimplexPreimageIndex X U x))) n ≫
    (ExcisionCoverSmall.coverMemberToSmallIntegralSingularChains X U
      (SubdivisionAffineSmall.coverSmallSimplexPreimageIndex X U x)).f (n + 1)

/-- The degree-raising affine prism operator on cover-small chains. -/
noncomputable def coverSmallAffinePrismComponent (n : ℕ) :
    (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n ⟶
      (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X (n + 1) :=
  Sigma.desc (coverSmallAffinePrismSimplexChain X U n)

@[reassoc (attr := simp)]
theorem iota_coverSmallAffinePrismComponent
    (n : ℕ)
    (x : (ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    (ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).ιChainComplex x ≫
        coverSmallAffinePrismComponent X U n =
      coverSmallAffinePrismSimplexChain X U n x := by
  apply Sigma.ι_comp_desc

/-- The small prism on a generator agrees with the full prism after inclusion. -/
theorem coverSmallAffinePrismSimplexChain_comp_inclusion
    (n : ℕ)
    (x : (ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n))) :
    coverSmallAffinePrismSimplexChain X U n x ≫
        (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f (n + 1) =
      (TopCat.toSSet.obj X).ιChainComplex x.1 ≫
        SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X n := by
  let j := SubdivisionAffineSmall.coverSmallSimplexPreimageIndex X U x
  let y := SubdivisionAffineSmall.coverSmallSimplexPreimage X U x
  let I := SSet.chainComplexMap
    (TopCat.toSSet.map (ExcisionCoverSmall.topologicalSubsetInclusion X (U j)))
    (AddCommGrpCat.of ℤ)
  have hcover := congrArg (fun F ↦ F.f (n + 1))
    (ExcisionCoverSmall.coverMemberToSmallIntegralSingularChains_comp_inclusion X U j)
  change (SSet.chainComplexMap (ExcisionCoverSmall.coverMemberToSmallSingularSet X U j)
        (AddCommGrpCat.of ℤ)).f (n + 1) ≫
      (SSet.chainComplexMap (ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) = I.f (n + 1) at hcover
  change (((TopCat.toSSet.obj (TopCat.of (U j))).ιChainComplex y ≫
      SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent (TopCat.of (U j)) n) ≫
        (SSet.chainComplexMap (ExcisionCoverSmall.coverMemberToSmallSingularSet X U j)
          (AddCommGrpCat.of ℤ)).f (n + 1)) ≫
      (SSet.chainComplexMap (ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) = _
  rw [Category.assoc, hcover, Category.assoc,
    ← SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent_naturality, ← Category.assoc,
    SSet.ι_chainComplexMap_f, show (TopCat.toSSet.map
      (ExcisionCoverSmall.topologicalSubsetInclusion X (U j))).app _ y = x.1 from
    SubdivisionAffineSmall.coverSmallSimplexPreimage_spec X U x]

/-- The small prism agrees degreewise with the full prism after inclusion. -/
theorem coverSmallAffinePrismComponent_comp_inclusion
    (n : ℕ) :
    coverSmallAffinePrismComponent X U n ≫
        (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f (n + 1) =
      (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U).f n ≫
        SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X n := by
  change coverSmallAffinePrismComponent X U n ≫
      (SSet.chainComplexMap (ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f (n + 1) =
    (SSet.chainComplexMap (ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
      (AddCommGrpCat.of ℤ)).f n ≫
      SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X n
  apply (ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_coverSmallAffinePrismComponent]
  simp only [SSet.ι_chainComplexMap_f_assoc]
  exact coverSmallAffinePrismSimplexChain_comp_inclusion X U n x

/-- The cover-small prism gives the chain-homotopy equation in positive degrees. -/
theorem coverSmallAffinePrismComponent_identity_succ
    (n : ℕ) :
    (SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U).f (n + 1) =
      (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).d (n + 1) n ≫
          coverSmallAffinePrismComponent X U n +
        coverSmallAffinePrismComponent X U (n + 1) ≫
          (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).d (n + 2) (n + 1) +
        𝟙 ((ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X (n + 1)) := by
  let I := SSet.chainComplexMap (ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
    (AddCommGrpCat.of ℤ)
  have : Mono I := by
    dsimp [I]
    exact ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion_mono X U
  have : Mono (I.f (n + 1)) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) (n + 1)).map I)
    infer_instance
  apply (cancel_mono (I.f (n + 1))).mp
  rw [Preadditive.add_comp, Preadditive.add_comp]
  simp only [Category.id_comp]
  rw [SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap_f]
  have hA := SubdivisionAffineSmall.coverSmallAffineSubdivisionComponent_comp_inclusion X U (n + 1)
  change SubdivisionAffineSmall.coverSmallAffineSubdivisionComponent X U (n + 1) ≫ I.f (n + 1) =
    I.f (n + 1) ≫ SubdivisionAffine.affineSingularSubdivisionComponent X (n + 1) at hA
  have hP (k : ℕ) :
      coverSmallAffinePrismComponent X U k ≫ I.f (k + 1) =
        I.f k ≫ SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X k :=
    coverSmallAffinePrismComponent_comp_inclusion X U k
  rw [hA]
  change I.f (n + 1) ≫
      (SubdivisionAffine.affineSingularSubdivisionChainMap X).f (n + 1) = _
  rw [SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent_identity_succ,
    Preadditive.comp_add, Preadditive.comp_add]
  simp only [Category.comp_id]
  apply congrArg₂ (fun a b ↦ a + b)
  · apply congrArg₂ (fun a b ↦ a + b)
    · rw [← Category.assoc, I.comm, Category.assoc, ← hP, ← Category.assoc]
    · rw [← Category.assoc, ← hP, Category.assoc, I.comm, ← Category.assoc]
  · rfl

/-- The cover-small prism gives the chain-homotopy equation in degree zero. -/
theorem coverSmallAffinePrismComponent_identity_zero :
    (SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U).f 0 =
      coverSmallAffinePrismComponent X U 0 ≫
          (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).d 1 0 +
        𝟙 ((ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X 0) := by
  let I := SSet.chainComplexMap (ExcisionCoverSmall.coverSmallSingularSubcomplex X U).ι
    (AddCommGrpCat.of ℤ)
  have : Mono I := by
    dsimp [I]
    exact ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion_mono X U
  have : Mono (I.f 0) := by
    change Mono ((HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) 0).map I)
    infer_instance
  apply (cancel_mono (I.f 0)).mp
  rw [Preadditive.add_comp]
  simp only [Category.id_comp]
  rw [SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap_f]
  have hA := SubdivisionAffineSmall.coverSmallAffineSubdivisionComponent_comp_inclusion X U 0
  change SubdivisionAffineSmall.coverSmallAffineSubdivisionComponent X U 0 ≫ I.f 0 =
    I.f 0 ≫ SubdivisionAffine.affineSingularSubdivisionComponent X 0 at hA
  have hP : coverSmallAffinePrismComponent X U 0 ≫ I.f 1 =
      I.f 0 ≫ SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent X 0 :=
    coverSmallAffinePrismComponent_comp_inclusion X U 0
  rw [hA]
  change I.f 0 ≫ (SubdivisionAffine.affineSingularSubdivisionChainMap X).f 0 = _
  rw [SubdivisionAffinePrism.affineSingularSubdivisionPrismComponent_identity_zero,
    Preadditive.comp_add]
  simp only [Category.comp_id]
  apply congrArg₂ (fun a b ↦ a + b)
  · rw [← Category.assoc, ← hP, Category.assoc, I.comm, ← Category.assoc]
  · rfl

/-- The degree-raising small-prism family. -/
noncomputable def coverSmallAffinePrismHom (i j : ℕ) :
    (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X i ⟶
      (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X j :=
  if h : j = i + 1 then by
    subst j
    exact coverSmallAffinePrismComponent X U i
  else 0

@[simp]
theorem coverSmallAffinePrismHom_succ (i : ℕ) :
    coverSmallAffinePrismHom X U i (i + 1) =
      coverSmallAffinePrismComponent X U i := by
  simp [coverSmallAffinePrismHom]

/-- Cover-small affine subdivision is chain homotopic to the identity. -/
noncomputable def coverSmallAffineSubdivisionHomotopy :
    Homotopy (SubdivisionAffineSmall.coverSmallAffineSubdivisionChainMap X U)
      (𝟙 (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U)) where
  hom := coverSmallAffinePrismHom X U
  zero i j hij := by
    rw [coverSmallAffinePrismHom]
    split_ifs with h
    · exfalso
      apply hij
      rw [ComplexShape.down_Rel]
      exact h.symm
    · rfl
  comm i := by
    cases i with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [coverSmallAffinePrismHom_succ, zero_add,
          HomologicalComplex.id_f]
        exact coverSmallAffinePrismComponent_identity_zero X U
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [coverSmallAffinePrismHom_succ,
          HomologicalComplex.id_f]
        exact coverSmallAffinePrismComponent_identity_succ X U n

end

end OAI.AlgebraicTopology.Singular.SubdivisionAffineSmallPrism
