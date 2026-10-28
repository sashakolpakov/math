/-
Copyright 2026 The Formal Conjectures Authors.

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
import OAI.AlgebraicTopology.Singular.SheafCochainAt
import OAI.AlgebraicTopology.SimplicialSet.ChainComplexSplit
import OAI.LinearAlgebra.Foundations.DualDefs
import Mathlib.Algebra.Module.Projective
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Sheaf Cochain Flasque -/

namespace OAI.AlgebraicTopology.Singular.SheafCochainFlasque

noncomputable section

/-!
# Flasqueness of open singular cochains

Restriction of a singular cochain to an open subset is surjective: the inclusion on singular
chains is a split injection, and the dual of a split injection is surjective. Consequently, the
presheaf of singular cochains in each fixed degree is flasque.

The extension may be chosen linearly. We also identify the cochains on the top open set with the
ordinary singular cochains of the ambient space. These statements concern the presheaf before
sheafification; no claim that sheafification preserves flasqueness is used.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- Inclusion of open subsets induces a monomorphism of singular chain complexes. -/
lemma openSingularChainComplexMap_mono {U V : Opens X} (i : U ⟶ V) :
    Mono ((SheafCochain.openSingularChainComplexFunctor R X).map i) := by
  let : Mono ((Opens.toTopCat X).map i) :=
    (TopCat.mono_iff_injective ((Opens.toTopCat X).map i)).mpr fun x y h ↦
      Subtype.ext (congrArg (fun z : V ↦ z.1) h)
  dsimp [SheafCochain.openSingularChainComplexFunctor]
  apply Functor.map_mono

/-- Inclusion of open subsets is injective on singular chains in every degree. -/
lemma openSingularChainMap_injective {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    Function.Injective (((SheafCochain.openSingularChainComplexFunctor R X).map i).f n).hom := by
  let : Mono ((SheafCochain.openSingularChainComplexFunctor R X).map i) :=
    openSingularChainComplexMap_mono R X i
  rw [← ModuleCat.mono_iff_injective]
  exact Functor.map_mono (HomologicalComplex.eval (ModuleCat R) _ n)
    ((SheafCochain.openSingularChainComplexFunctor R X).map i)

/-- Inclusion of open subsets induces a split monomorphism on singular chains in each degree. -/
lemma openSingularChainMap_isSplitMono {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    IsSplitMono (((SheafCochain.openSingularChainComplexFunctor R X).map i).f n) :=
  let _ : Mono ((Opens.toTopCat X).map i) :=
    (TopCat.mono_iff_injective ((Opens.toTopCat X).map i)).mpr fun _ _ h ↦
      Subtype.ext (congrArg (fun z : V ↦ z.1) h)
  SimplicialSet.ChainComplexSplit.isSplitMono_singularChainComplexFunctor_map_f
    ((Opens.toTopCat X).map i) (ModuleCat.of R R) n

/-- Every cochain on an open subset extends linearly to a containing open subset. -/
lemma openSingularCochainRestriction_surjective
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    Function.Surjective
      ((SheafCochain.singularCochainPresheaf R X n).map i) :=
  let _ := openSingularChainMap_isSplitMono R X i.unop n
  OAI.LinearAlgebra.Foundations.DualDefs.LinearMap.dualMap_surjective_of_comp_eq_id
    (congrArg ModuleCat.Hom.hom
      (IsSplitMono.id (((SheafCochain.openSingularChainComplexFunctor R X).map i.unop).f n)))

/-- The presheaf of singular cochains in every fixed degree is flasque. -/
instance singularCochainPresheaf_isFlasque (n : ℕ) :
    TopCat.Presheaf.IsFlasque (SheafCochain.singularCochainPresheaf R X n) where
  epi i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact openSingularCochainRestriction_surjective R X i n

end

end OAI.AlgebraicTopology.Singular.SheafCochainFlasque
