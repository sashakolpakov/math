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
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import OAI.LinearAlgebra.Foundations.QuotientBasic
import OAI.LinearAlgebra.Foundations.DualDefs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Linear Dual -/

namespace OAI.Algebra.Homology.LinearDual

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.ShortComplex
open _root_.HomologicalComplex

/-!
# The linear dual of a complex of modules

Applying the dual degreewise turns a nonnegatively graded chain complex into a cochain complex,
whose degree-`n` short complex is the reversed dual of the original one. Duality is
contravariantly functorial for maps, isomorphisms, chain homotopies and chain-homotopy
equivalences, so all of these transport to the dual cochain complex. That much holds over a
commutative ring.

Over a field the homology of the reversed dual is canonically the dual of the homology, with no
finite-dimensionality hypothesis: this is `linearDualHomologyEquiv`. Over a ring the comparison
map `dualHomologyComparisonExplicit` still exists but need not be bijective. Each namespace below
is split into a `CommRing` section and a `Field` section accordingly.
-/

open Limits

universe u

namespace CategoryTheory.ShortComplex

section CommRing
variable {R : Type u} [CommRing R]

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

/-- Let `R` be a commutative ring and `S` a sequence `A → B → C` of `R`-modules with zero composite.
Its reversed dual is the sequence `Hom_R(C,R) → Hom_R(B,R) → Hom_R(A,R)`, whose maps precompose
with those of `S`. -/
abbrev linearDual (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk S.g.hom.dualMap S.f.hom.dualMap (by ext; simp)

/-- Let `R` be a commutative ring and `A → B → C` a sequence of modules with zero composite. A
functional on `B` vanishing on the image of `A` restricts to cycles and descends to `ker(B →
C)/im(A → B)`. This is the resulting linear map from dual cycles to functionals on homology. -/
@[simps]
def dualCycleToHomologyFunctional (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.f.hom.dualMap →ₗ[R]
      Module.Dual R S.moduleCatLeftHomologyData.H where
  toFun φ := (LinearMap.range S.moduleCatToCycles).liftQ
    (φ.1.comp (LinearMap.ker S.g.hom).subtype) (by
      rintro _ ⟨x, rfl⟩
      have := LinearMap.congr_fun (LinearMap.mem_ker.1 φ.2) x
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
      simpa [moduleCatToCycles, S.f.hom.codRestrict_apply S.g.hom.ker (h := moduleCat_zero_apply S)])
  map_add' φ ψ := by
    generalize_proofs
    simp [LinearMap.add_comp, OAI.LinearAlgebra.Foundations.QuotientBasic.Submodule.liftQ_add S.moduleCatToCycles.range, *]
  map_smul' a φ := by
    generalize_proofs
    simp [LinearMap.smul_comp, OAI.LinearAlgebra.Foundations.QuotientBasic.Submodule.liftQ_smul S.moduleCatToCycles.range, *]

lemma dualCycleToHomologyFunctional_vanishes_on_boundaries
    (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.range ((linearDual S).moduleCatToCycles) ≤
      LinearMap.ker (dualCycleToHomologyFunctional S) := by
  rintro _ ⟨(ψ : Module.Dual R S.X₃), rfl⟩
  simp [dualCycleToHomologyFunctional]
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H z => simp [moduleCatToCycles, S.g.hom.dualMap_apply]

/-- Let `R` be a commutative ring and `S = (A → B → C)` a sequence of modules with zero composite.
This linear map from the homology of the reversed dual to `Hom_R(H(S), R)` pairs the class of a
functional `φ` with the class of a cycle `z` by `φ(z)`, using quotient modules for both homology
groups. -/
def dualHomologyComparisonExplicit (S : ShortComplex (ModuleCat.{u} R)) :
    (linearDual S).moduleCatLeftHomologyData.H →ₗ[R]
      Module.Dual R S.moduleCatLeftHomologyData.H :=
  (LinearMap.range (linearDual S).moduleCatToCycles).liftQ
    (dualCycleToHomologyFunctional S)
    (dualCycleToHomologyFunctional_vanishes_on_boundaries S)

@[simp]
lemma dualHomologyComparisonExplicit_mk_apply_mk
    (S : ShortComplex (ModuleCat.{u} R))
    (φ : LinearMap.ker S.f.hom.dualMap) (z : LinearMap.ker S.g.hom) :
    (dualHomologyComparisonExplicit S) (Submodule.Quotient.mk φ)
        (Submodule.Quotient.mk z) = φ.1 z.1 :=
  rfl

end CommRing

variable {R : Type u} [Field R]

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

lemma dualHomologyComparisonExplicit_surjective
    (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Surjective (dualHomologyComparisonExplicit S) := by
  intro α
  let φ : Module.Dual R S.X₂ :=
    Subspace.dualLift (LinearMap.ker S.g.hom) <| α.comp (LinearMap.range S.moduleCatToCycles).mkQ
  have hφ : φ ∈ LinearMap.ker S.f.hom.dualMap := LinearMap.mem_ker.2 <| LinearMap.ext fun x ↦ by
    simpa [φ, Subspace.dualLift_of_mem (LinearMap.mem_ker.2 <| S.moduleCat_zero_apply x)] using!
      congr(α $((Submodule.Quotient.mk_eq_zero _).2 <| S.moduleCatToCycles.mem_range_self x))
  refine ⟨Submodule.Quotient.mk ⟨φ, hφ⟩, ?_⟩
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ z => simp +zetaDelta [Submodule.mkQ_apply _]

lemma dualHomologyComparisonExplicit_injective
    (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Injective (dualHomologyComparisonExplicit S) := by
  intro a b hab
  induction a using Submodule.Quotient.induction_on with
  | _ φ =>
    induction b using Submodule.Quotient.induction_on with
    | _ ψ =>
      rw [Submodule.Quotient.eq]
      have hzero : (dualCycleToHomologyFunctional S) (φ - ψ) = 0 :=
        ((dualCycleToHomologyFunctional S).map_sub φ ψ).trans (sub_eq_zero.2 hab)
      have hv : (φ - ψ).1 ∈ (LinearMap.ker S.g.hom).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro z hz
        exact LinearMap.congr_fun hzero (Submodule.Quotient.mk ⟨z, hz⟩)
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hv
      obtain ⟨η, hη⟩ := hv
      exact ⟨η, Subtype.ext hη⟩

/-- Let `R` be a field and `S = (A → B → C)` a sequence of vector spaces with zero composite.
Evaluation of a dual cocycle on a cycle gives this linear equivalence `H(S*) ≃ Hom_R(H(S), R)`,
where `S*` is the reversed dual sequence. It holds without a finite-dimensionality assumption. -/
def linearDualHomologyEquiv (S : ShortComplex (ModuleCat.{u} R)) :
    (linearDual S).homology ≃ₗ[R] Module.Dual R S.homology :=
  (linearDual S).moduleCatHomologyIso.toLinearEquiv.trans <|
    (LinearEquiv.ofBijective (dualHomologyComparisonExplicit S)
      ⟨(dualHomologyComparisonExplicit_injective S),
        (dualHomologyComparisonExplicit_surjective S)⟩).trans <|
      S.moduleCatHomologyIso.toLinearEquiv.dualMap

end CategoryTheory.ShortComplex

namespace HomologicalComplex

section CommRing
variable {R : Type u} [CommRing R]

/-- Let `R` be a commutative ring and `K` a chain complex of `R`-modules in nonnegative degrees. Its
dual cochain complex has `Hom_R(K_n, R)` in degree `n`, with coboundary `φ ↦ φ ∘ ∂`, where `∂:
K_{n+1} → K_n` is the boundary of `K`. -/
@[implicit_reducible, simps -isSimp X d]
def linearDualCochainComplex (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ where
  X n := ModuleCat.of R (Module.Dual R (K.X n))
  d i j := ModuleCat.ofHom (K.d j i).hom.dualMap
  shape i j := by simp +contextual
  d_comp_d' i j k h1 h2 := by
    simp [← ModuleCat.ofHom_comp, LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp]

attribute [simp] HomologicalComplex.linearDualCochainComplex_X

@[simp]
lemma linearDualCochainComplex_d_succ (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    ((linearDualCochainComplex K)).d n (n + 1) =
      ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap := rfl

attribute [local implicit_reducible] shortComplexFunctor' shortComplexFunctor
/-- Let `R` be a commutative ring and `K` a nonnegative chain complex of `R`-modules. For each `n`,
this identifies the three terms around degree `n` in the dual cochain complex with the reversed
linear duals of the three terms around `n` in `K`, including the adjacent differentials. -/
@[implicit_reducible]
def linearDualCochainComplexScIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (linearDualCochainComplex K).sc n ≅ (CategoryTheory.ShortComplex.linearDual (K.sc n)) :=
  have hprev : (ComplexShape.up ℕ).prev n = (ComplexShape.down ℕ).next n := by cases n <;> simp
  have hnext : (ComplexShape.up ℕ).next n = (ComplexShape.down ℕ).prev n := by simp
  (linearDualCochainComplex K).isoSc' (c := ComplexShape.up ℕ) _ _ _ hprev hnext --≪≫

variable {K L M : ChainComplex (ModuleCat.{u} R) ℕ}

/-- Let `R` be a commutative ring and `f: K → L` a map of nonnegative chain complexes of
`R`-modules. This map of dual cochain complexes `L* → K*` sends a degree-`n` functional `φ` to
`φ ∘ f_n`. -/
@[implicit_reducible, simps f]
def linearDualMap (f : K ⟶ L) :
    (linearDualCochainComplex L) ⟶ (linearDualCochainComplex K) where
  f n := ModuleCat.ofHom (f.f n).hom.dualMap
  comm' _ _ _ := by
    rw [linearDualCochainComplex_d, linearDualCochainComplex_d, ← ModuleCat.ofHom_comp,
      LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, ← ModuleCat.ofHom_comp,
      LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, f.comm]

@[simp]
lemma linearDualMap_id (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    linearDualMap (𝟙 K) = 𝟙 (linearDualCochainComplex K) :=
  rfl

@[simp]
lemma linearDualMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    linearDualMap (f ≫ g) = linearDualMap g ≫ linearDualMap f :=
  rfl

/-- Let `R` be a commutative ring and `e: K ≅ L` an isomorphism of nonnegative chain complexes of
`R`-modules. Precomposition with `e` gives this isomorphism of dual cochain complexes `L* ≅ K*`,
with inverse given by precomposition with `e⁻¹`. -/
@[implicit_reducible]
def linearDualIso (e : K ≅ L) :
    (linearDualCochainComplex L) ≅ (linearDualCochainComplex K) where
  hom := linearDualMap e.hom
  inv := linearDualMap e.inv
  hom_inv_id := by rw [← linearDualMap_comp, e.inv_hom_id, linearDualMap_id]
  inv_hom_id := by rw [← linearDualMap_comp, e.hom_inv_id, linearDualMap_id]

end CommRing

variable {R : Type u} [Field R]

/-- Let `R` be a field and `K` a nonnegative chain complex of `R`-vector spaces. Evaluation of
cocycles on cycles gives this linear equivalence `H^n(Hom_R(K,R)) ≃ Hom_R(H_n(K), R)`. It
requires no finite-dimensionality assumption. -/
def linearDualHomologyEquiv (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (linearDualCochainComplex K).homology n ≃ₗ[R] Module.Dual R (K.homology n) :=
  (ShortComplex.homologyMapIso (linearDualCochainComplexScIso K n)).toLinearEquiv.trans
    (CategoryTheory.ShortComplex.linearDualHomologyEquiv (K.sc n))

end HomologicalComplex

end

end OAI.Algebra.Homology.LinearDual
