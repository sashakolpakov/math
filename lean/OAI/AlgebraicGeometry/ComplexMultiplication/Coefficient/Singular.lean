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
import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Chains
import OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Singular -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Singular.SingularCoefficients

noncomputable section

/-! # Singular cochains with general field coefficients -/

open _root_.CategoryTheory Limits _root_.TopologicalSpace OAI.AlgebraicTopology.Singular
open OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Chains.SingularCoefficients
open OAI.AlgebraicTopology.Singular.Cohomology
open OAI.AlgebraicTopology.Singular.SheafSubdivisionCochain
open scoped Simplicial

variable (K : Type) [Field K]

section Cover
variable {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

/-- Restriction of coefficient singular cochains to chains subordinate to a family of subsets. -/
def coefficientCochainRestrictionToCoverSmall :
    (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of K K))) ⟶
      (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (CoverSmallCoefficientSingularChainComplex K Y U)) :=
  Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap (Chains.SingularCoefficients.coverSmallCoefficientSingularChainInclusion K Y U)

/-- The chain map from one member of a family into the cover-small coefficient chains. -/
def coverMemberToSmallCoefficientSingularChains (j : κ) :
    (TopCat.toSSet.obj (TopCat.of (U j))).chainComplex (ModuleCat.of K K) ⟶
      Chains.SingularCoefficients.CoverSmallCoefficientSingularChainComplex K Y U :=
  SSet.chainComplexMap (AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallSingularSet Y U j) (ModuleCat.of K K)

/-- Restriction to cover-small coefficient chains is surjective in every cochain degree. -/
lemma coefficientCochainRestrictionToCoverSmall_surjective (n : ℕ) :
    Function.Surjective ((coefficientCochainRestrictionToCoverSmall K Y U).f n) := by
  apply LinearMap.dualMap_surjective_of_injective
  rw [← ModuleCat.mono_iff_injective]
  exact Functor.map_mono
    (HomologicalComplex.eval (ModuleCat K) (ComplexShape.down ℕ) n)
    (Chains.SingularCoefficients.coverSmallCoefficientSingularChainInclusion K Y U)

/-- Restriction to cover-small coefficient chains is an epimorphism of cochain complexes. -/
instance coefficientCochainRestrictionToCoverSmall_epi :
    Epi (coefficientCochainRestrictionToCoverSmall K Y U) :=
  HomologicalComplex.epi_of_epi_f _ fun n ↦ by
    rw [ModuleCat.epi_iff_surjective]
    exact coefficientCochainRestrictionToCoverSmall_surjective K Y U n

/-- An open cover gives a homotopy equivalence from all coefficient cochains to its cover-small
cochains. -/
def coefficientCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of K K)))
      (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (CoverSmallCoefficientSingularChainComplex K Y U)) :=
  Algebra.Homology.LinearDualHomotopy.HomologicalComplex.linearDualHomotopyEquiv
    (Chains.SingularCoefficients.coverSmallCoefficientChainHomotopyEquiv_of_openCover K Y U hUopen hUcover)

/-- Restriction from cochains on the top open subset to chains subordinate to a family of
subsets. -/
def topOpenCoefficientCochainRestrictionToCoverSmall :
    (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (TopOpenSingularChainComplex K Y)) ⟶
      (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (CoverSmallCoefficientSingularChainComplex K Y U)) :=
  (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen K Y).inv ≫
    coefficientCochainRestrictionToCoverSmall K Y U

instance topOpenCoefficientCochainRestrictionToCoverSmall_epi :
    Epi (topOpenCoefficientCochainRestrictionToCoverSmall K Y U) := by
  apply HomologicalComplex.epi_of_epi_f _ fun n ↦ ?_
  rw [ModuleCat.epi_iff_surjective]
  have h₁ : Function.Surjective
      ((AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen K Y).inv.f n) := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  have h₂ := coefficientCochainRestrictionToCoverSmall_surjective K Y U n
  intro z
  obtain ⟨y, hy⟩ := h₂ z
  obtain ⟨x, hx⟩ := h₁ y
  refine ⟨x, ?_⟩
  change (coefficientCochainRestrictionToCoverSmall K Y U).f n
      ((AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen K Y).inv.f n x) = z
  rw [hx, hy]

@[reassoc]
lemma coverMemberToSmallCoefficientSingularChains_comp_inclusion (j : κ) :
    coverMemberToSmallCoefficientSingularChains K Y U j ≫
        Chains.SingularCoefficients.coverSmallCoefficientSingularChainInclusion K Y U =
      SSet.chainComplexMap
        (TopCat.toSSet.map (AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion Y (U j)))
        (ModuleCat.of K K) := by
  change ((SSet.chainComplexFunctor (ModuleCat K)).obj
      (ModuleCat.of K K)).map (AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallSingularSet Y U j) ≫
    ((SSet.chainComplexFunctor (ModuleCat K)).obj
      (ModuleCat.of K K)).map (AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex Y U).ι = _
  rw [← Functor.map_comp, AlgebraicTopology.Singular.ExcisionCoverSmall.coverMemberToSmallSingularSet_comp_inclusion]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on every member of a covering sieve implies vanishing on all chains subordinate
to the associated family of open subsets. -/
lemma coefficientCochainRestrictionToCoveringSieve_eq_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of K K))).X n)
    (hφ : ∀ I : S.Arrow,
      (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf K Y n).map I.f.op
        ((AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen K Y).hom.f n φ) = 0) :
    (coefficientCochainRestrictionToCoverSmall K Y
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S)).f n φ = 0 := by
  change Module.Dual K
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K)).X n) at φ
  apply_fun ModuleCat.ofHom
  apply SSet.chainComplex_hom_ext
  intro x
  obtain ⟨I, y, hy⟩ :=
    (AlgebraicTopology.Singular.ExcisionCoverSmall.mem_coverSmallSingularSubcomplex_iff_exists_preimage Y
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S) x.1).mp x.2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hI := congrArg
    (fun ψ : AlgebraicTopology.Singular.SheafCochain.OpenCochains K Y (.op I.Y) n ↦ ψ
      (((TopCat.toSSet.obj (TopCat.of (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of K K) y).hom a))
    (hφ I)
  change φ (ModuleCat.Hom.hom
      (((AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor K Y).map I.f).f n ≫
        (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso K Y).hom.f n)
      (((TopCat.toSSet.obj (TopCat.of (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of K K) y).hom a)) = 0 at hI
  have hchain := HomologicalComplex.congr_hom
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.openSingularChainToTop_comp_topOpenIso K Y I.f) n
  have hchain' :
      ((AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor K Y).map I.f).f n ≫
          (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso K Y).hom.f n =
        (SSet.chainComplexMap
          (TopCat.toSSet.map (AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion Y I.Y))
          (ModuleCat.of K K)).f n := by
    simpa only [HomologicalComplex.comp_f] using hchain
  rw [hchain'] at hI
  have hiota := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f
      (TopCat.toSSet.obj (TopCat.of (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S I)))
      (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map (AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion Y
        (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S I)))
      (ModuleCat.of K K) y) a
  have hI' : φ
      (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of K K)
        ((TopCat.toSSet.map (AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion Y
          (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S I))).app _ y)).hom a) = 0 := by
    calc
      _ = φ ((SSet.chainComplexMap
          (TopCat.toSSet.map (AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion Y
            (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S I)))
          (ModuleCat.of K K)).f n
          (((TopCat.toSSet.obj
            (TopCat.of (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S I))).ιChainComplex
              (R := ModuleCat.of K K) y).hom a)) := congrArg φ hiota.symm
      _ = 0 := hI
  change φ (ModuleCat.Hom.hom
    (((AlgebraicTopology.Singular.ExcisionCoverSmall.coverSmallSingularSubcomplex Y
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S) : SSet).ιChainComplex
        (R := ModuleCat.of K K) x) ≫
      (Chains.SingularCoefficients.coverSmallCoefficientSingularChainInclusion K Y
        (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S)).f n) a) = 0
  dsimp only [Chains.SingularCoefficients.coverSmallCoefficientSingularChainInclusion] at ⊢
  simpa [hy] using hI'
  · intro f g h
    exact congrArg ModuleCat.Hom.hom h

set_option backward.isDefEq.respectTransparency false in
/-- Conversely, vanishing on the cover-small chains associated to a covering sieve implies
vanishing after restriction along every arrow of that sieve. -/
lemma coefficientCochainRestrictionToCoveringSieve_local_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of K K))).X n)
    (hφ : (coefficientCochainRestrictionToCoverSmall K Y
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S)).f n φ = 0) :
    ∀ I : S.Arrow,
      (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf K Y n).map I.f.op
        ((AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen K Y).hom.f n φ) = 0 := by
  intro I
  change Module.Dual K
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K)).X n) at φ
  apply LinearMap.ext
  intro c
  have hc := LinearMap.congr_fun hφ
    (((coverMemberToSmallCoefficientSingularChains K Y
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S) I).f n).hom c)
  have htop := HomologicalComplex.congr_hom
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.openSingularChainToTop_comp_topOpenIso K Y I.f) n
  have hmember := HomologicalComplex.congr_hom
    (coverMemberToSmallCoefficientSingularChains_comp_inclusion K Y
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S) I) n
  calc
    φ ((AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenSingularChainComplexIso K Y).hom.f n
        (((AlgebraicTopology.Singular.SheafCochain.openSingularChainComplexFunctor K Y).map I.f).f n c)) =
      φ ((SSet.chainComplexMap
        (TopCat.toSSet.map (AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion Y I.Y))
        (ModuleCat.of K K)).f n c) :=
          congrArg φ (ConcreteCategory.congr_hom htop c)
    _ = φ ((Chains.SingularCoefficients.coverSmallCoefficientSingularChainInclusion K Y
          (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S)).f n
        ((coverMemberToSmallCoefficientSingularChains K Y
          (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S) I).f n c)) :=
            congrArg φ (ConcreteCategory.congr_hom hmember c).symm
    _ = 0 := hc

lemma coefficientCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coefficientCochainHomotopyEquivCoverSmall K Y U hUopen hUcover).hom =
      coefficientCochainRestrictionToCoverSmall K Y U := by
  dsimp [coefficientCochainHomotopyEquivCoverSmall,
    coefficientCochainRestrictionToCoverSmall]
  change Algebra.Homology.LinearDual.HomologicalComplex.linearDualMap
      (Chains.SingularCoefficients.coverSmallCoefficientChainHomotopyEquiv_of_openCover K
        Y U hUopen hUcover).hom = _
  rw [Chains.SingularCoefficients.coverSmallCoefficientChainHomotopyEquiv_of_openCover_hom K]

/-- Restriction from all coefficient cochains to cover-small cochains is a quasi-isomorphism for an
open cover. -/
theorem coefficientCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (coefficientCochainRestrictionToCoverSmall K Y U) := by
  rw [← coefficientCochainHomotopyEquivCoverSmall_hom K Y U hUopen hUcover]
  infer_instance

/-- The complex of coefficient cochains vanishing on every chain subordinate to an open cover is
acyclic. -/
theorem coefficientCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (coefficientCochainRestrictionToCoverSmall K Y U)).Acyclic := by
  let := coefficientCochainRestrictionToCoverSmall_quasiIso K Y U hUopen hUcover
  exact Algebra.Homology.KernelAcyclic.HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (coefficientCochainRestrictionToCoverSmall K Y U)

set_option backward.isDefEq.respectTransparency false in
/-- A closed coefficient cochain which vanishes on all cover-small chains has a primitive which
also vanishes on all cover-small chains. -/
theorem exists_coverSmallKernel_primitive
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ)
    (φ : (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of K K))).X n)
    (hφsmall : (coefficientCochainRestrictionToCoverSmall K Y U).f n φ = 0)
    (hφclosed : ((Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of K K))).d n (n + 1)) φ = 0) :
    ∃ ψ : (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of K K))).X
          ((ComplexShape.up ℕ).prev n),
      ((Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of K K))).sc n).f ψ = φ ∧
        (coefficientCochainRestrictionToCoverSmall K Y U).f
          ((ComplexShape.up ℕ).prev n) ψ = 0 := by
  let F := (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex ((TopCat.toSSet.obj Y).chainComplex
    (ModuleCat.of K K)))
  let q := coefficientCochainRestrictionToCoverSmall K Y U
  let L := kernel q
  let E : (kernel q).X n ≅ ModuleCat.of K (q.f n).hom.ker :=
    asIso (kernelComparison q (HomologicalComplex.eval (ModuleCat K)
      (ComplexShape.up ℕ) n)) ≪≫ ModuleCat.kernelIsoKer (q.f n)
  let z : (kernel q).X n := E.inv ⟨φ, hφsmall⟩
  have hzmap : (kernel.ι q).f n z = φ := by
    let ev := HomologicalComplex.eval (ModuleCat K) (ComplexShape.up ℕ) n
    have hc := ConcreteCategory.congr_hom (kernelComparison_comp_ι q ev) z
    have hk := ModuleCat.kernelIsoKer_hom_ker_subtype_apply
      (q.f n) ((kernelComparison q ev) z)
    have hE : E.hom z = (⟨φ, hφsmall⟩ : (q.f n).hom.ker) := by
      simp [z]
    calc
      (kernel.ι q).f n z = kernel.ι (ev.map q) ((kernelComparison q ev) z) := hc.symm
      _ = ((ModuleCat.kernelIsoKer (q.f n)).hom
          ((kernelComparison q ev) z)).1 := hk.symm
      _ = φ := congrArg Subtype.val hE
  have hzclosed : (L.sc n).g z = 0 := by
    change L.d n ((ComplexShape.up ℕ).next n) z = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    apply (ModuleCat.mono_iff_injective ((kernel.ι q).f (n + 1))).mp inferInstance
    rw [map_zero]
    change (L.d n (n + 1) ≫ (kernel.ι q).f (n + 1)) z = 0
    rw [← (kernel.ι q).comm n (n + 1)]
    change F.d n (n + 1) ((kernel.ι q).f n z) = 0
    rw [hzmap]
    exact hφclosed
  have hacyclic := coefficientCoverSmallCochainKernel_acyclic K Y U hUopen hUcover
  obtain ⟨p, hp⟩ := (ShortComplex.moduleCat_exact_iff (L.sc n)).mp
    (hacyclic n) z hzclosed
  change L.d ((ComplexShape.up ℕ).prev n) n p = z at hp
  refine ⟨(kernel.ι q).f ((ComplexShape.up ℕ).prev n) p, ?_, ?_⟩
  · change F.d ((ComplexShape.up ℕ).prev n) n
      ((kernel.ι q).f ((ComplexShape.up ℕ).prev n) p) = φ
    calc
      _ = (kernel.ι q).f n
          (L.d ((ComplexShape.up ℕ).prev n) n p) :=
        by
          simpa only [ConcreteCategory.comp_apply, F, L] using
            (ConcreteCategory.congr_hom
              ((kernel.ι q).comm ((ComplexShape.up ℕ).prev n) n) p)
      _ = φ := by rw [hp, hzmap]
  · have hcondition := HomologicalComplex.congr_hom (kernel.condition q)
      ((ComplexShape.up ℕ).prev n)
    exact ConcreteCategory.congr_hom hcondition p

set_option backward.isDefEq.respectTransparency false in
/-- A closed cochain on the top open which vanishes along a covering sieve has a primitive that
still vanishes along the same sieve. -/
theorem exists_topOpenLocallyZero_primitive
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (TopOpenSingularChainComplex K Y)).X n)
    (hφlocal : ∀ I : S.Arrow,
      (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf K Y n).map I.f.op φ = 0)
    (hφclosed : ((Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (TopOpenSingularChainComplex K Y)).d
      n (n + 1)) φ = 0) :
    ∃ ψ : (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (TopOpenSingularChainComplex K Y)).X
        ((ComplexShape.up ℕ).prev n),
      ((Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (TopOpenSingularChainComplex K Y)).sc n).f ψ = φ ∧
        ∀ I : S.Arrow,
          (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf K Y ((ComplexShape.up ℕ).prev n)).map I.f.op ψ = 0 := by
  let A := (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (AlgebraicTopology.Singular.Cohomology.SingularChainComplex K Y))
  let B := (Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (TopOpenSingularChainComplex K Y))
  let e := AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen K Y
  let φ' : A.X n := e.inv.f n φ
  have heφ : e.hom.f n φ' = φ := by
    have hc := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom e.inv_hom_id n) φ
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
      HomologicalComplex.id_f, ConcreteCategory.id_apply, φ'] using hc
  have hlocal' : ∀ I : S.Arrow,
      (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf K Y n).map I.f.op (e.hom.f n φ') = 0 := by
    intro I
    rw [heφ]
    exact hφlocal I
  have hsmall : (coefficientCochainRestrictionToCoverSmall K Y
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S)).f n φ' = 0 :=
    coefficientCochainRestrictionToCoveringSieve_eq_zero K Y S n φ' hlocal'
  have hclosed' : A.d n (n + 1) φ' = 0 := by
    change A.d n (n + 1) (e.inv.f n φ) = 0
    have hc := ConcreteCategory.congr_hom (e.inv.comm n (n + 1)) φ
    calc
      _ = e.inv.f (n + 1) (B.d n (n + 1) φ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = 0 := by rw [hφclosed, map_zero]
  obtain ⟨ψ, hψ, hψsmall⟩ := exists_coverSmallKernel_primitive K Y
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily Y S)
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily_isOpen Y S)
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.coveringSieveOpenFamily_iUnion Y S) n φ' hsmall hclosed'
  refine ⟨e.hom.f ((ComplexShape.up ℕ).prev n) ψ, ?_, ?_⟩
  · change B.d ((ComplexShape.up ℕ).prev n) n
      (e.hom.f ((ComplexShape.up ℕ).prev n) ψ) = φ
    have hc := ConcreteCategory.congr_hom
      (e.hom.comm ((ComplexShape.up ℕ).prev n) n) ψ
    calc
      _ = e.hom.f n (A.d ((ComplexShape.up ℕ).prev n) n ψ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = e.hom.f n φ' := congrArg (e.hom.f n) hψ
      _ = φ := heφ
  · simpa only [e] using
      (coefficientCochainRestrictionToCoveringSieve_local_zero K
        Y S ((ComplexShape.up ℕ).prev n) ψ hψsmall)

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the map from top-open coefficient cochains to global first-plus cochains is
acyclic. -/
theorem topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic :
    (kernel (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainPlusComplex K Y)).Acyclic := by
  let C := AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex K Y
  let B := AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenForgottenSingularCochainComplex K Y
  let e := AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso K Y
  let f := AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainPlusComplex K Y
  let L := kernel f
  intro n
  rw [L.exactAt_iff, ShortComplex.ab_exact_iff]
  intro z hzclosed
  let φ : AlgebraicTopology.Singular.SheafCochain.OpenCochains K Y (.op ⊤) n := (kernel.ι f).f n z
  have hφplus : f.f n φ = 0 := by
    have hcondition := HomologicalComplex.congr_hom (kernel.condition f) n
    exact ConcreteCategory.congr_hom hcondition z
  obtain ⟨S, hφlocal⟩ :=
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochain_toPlus_eq_zero_iff K Y ⊤ n φ).mp hφplus
  have hφclosed : ((Algebra.Homology.LinearDual.HomologicalComplex.linearDualCochainComplex (TopOpenSingularChainComplex K Y)).d
      n (n + 1)) φ = 0 := by
    change L.d n ((ComplexShape.up ℕ).next n) z = 0 at hzclosed
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp] at hzclosed
    apply_fun (kernel.ι f).f (n + 1) at hzclosed
    rw [map_zero] at hzclosed
    have hc := ConcreteCategory.congr_hom ((kernel.ι f).comm n (n + 1)) z
    have hC : C.d n (n + 1) φ = 0 := by
      calc
        _ = (kernel.ι f).f (n + 1) (L.d n (n + 1) z) := by
          simpa only [ConcreteCategory.comp_apply, C, L] using hc
        _ = 0 := hzclosed
    change B.d n (n + 1) φ = 0
    have hc := ConcreteCategory.congr_hom (e.hom.comm n (n + 1)) φ
    have hc' : B.d n (n + 1) φ = C.d n (n + 1) φ := by
      simp only [ConcreteCategory.comp_apply] at hc
      simpa only [e, B, C,
        AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso_hom_f_apply] using hc
    rw [hc', hC]
  obtain ⟨ψ, hψ, hψlocal⟩ :=
    exists_topOpenLocallyZero_primitive K Y S n φ hφlocal hφclosed
  have hψplus : f.f ((ComplexShape.up ℕ).prev n) ψ = 0 := by
    change ((Opens.grothendieckTopology Y).toPlus
      (AlgebraicTopology.Singular.SheafCochain.singularCochainPresheaf K Y ((ComplexShape.up ℕ).prev n))).app
        (.op ⊤) ψ = 0
    exact (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochain_toPlus_eq_zero_iff K Y ⊤
      ((ComplexShape.up ℕ).prev n) ψ).mpr ⟨S, hψlocal⟩
  let ev := HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ)
    ((ComplexShape.up ℕ).prev n)
  let E : L.X ((ComplexShape.up ℕ).prev n) ≅
      AddCommGrpCat.of (f.f ((ComplexShape.up ℕ).prev n)).hom.ker :=
    asIso (kernelComparison f ev) ≪≫
      AddCommGrpCat.kernelIsoKer (f.f ((ComplexShape.up ℕ).prev n))
  let p : L.X ((ComplexShape.up ℕ).prev n) := E.inv ⟨ψ, hψplus⟩
  have hpmap : (kernel.ι f).f ((ComplexShape.up ℕ).prev n) p = ψ := by
    have hc := ConcreteCategory.congr_hom (kernelComparison_comp_ι f ev) p
    have hk := ConcreteCategory.congr_hom
      (AddCommGrpCat.kernelIsoKer_hom_comp_subtype
        (f.f ((ComplexShape.up ℕ).prev n))) ((kernelComparison f ev) p)
    have hE : E.hom p =
        (⟨ψ, hψplus⟩ : (f.f ((ComplexShape.up ℕ).prev n)).hom.ker) := by
      simp [p]
    calc
      (kernel.ι f).f ((ComplexShape.up ℕ).prev n) p =
          kernel.ι (ev.map f) ((kernelComparison f ev) p) := hc.symm
      _ = ((AddCommGrpCat.kernelIsoKer
          (f.f ((ComplexShape.up ℕ).prev n))).hom
            ((kernelComparison f ev) p)).1 := hk.symm
      _ = ψ := congrArg Subtype.val hE
  refine ⟨p, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective ((kernel.ι f).f n)).mp inferInstance
  have hc := ConcreteCategory.congr_hom
    ((kernel.ι f).comm ((ComplexShape.up ℕ).prev n) n) p
  have hψC : C.d ((ComplexShape.up ℕ).prev n) n ψ = φ := by
    change B.d ((ComplexShape.up ℕ).prev n) n ψ = φ at hψ
    have hc := ConcreteCategory.congr_hom
      (e.hom.comm ((ComplexShape.up ℕ).prev n) n) ψ
    have hc' : B.d ((ComplexShape.up ℕ).prev n) n ψ =
        C.d ((ComplexShape.up ℕ).prev n) n ψ := by
      simp only [ConcreteCategory.comp_apply] at hc
      simpa only [e, B, C,
        AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso_hom_f_apply] using hc
    exact hc'.symm.trans hψ
  calc
    (kernel.ι f).f n (L.d ((ComplexShape.up ℕ).prev n) n p) =
        C.d ((ComplexShape.up ℕ).prev n) n
          ((kernel.ι f).f ((ComplexShape.up ℕ).prev n) p) := by
      simpa only [ConcreteCategory.comp_apply, C, L] using hc.symm
    _ = C.d ((ComplexShape.up ℕ).prev n) n ψ := by rw [hpmap]
    _ = φ := hψC
    _ = (kernel.ι f).f n z := rfl

/-- The map from top-open coefficient cochains to global first-plus cochains is a
quasi-isomorphism. -/
theorem topOpenToGlobalSingularCochainPlusComplex_quasiIso :
    QuasiIso (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainPlusComplex K Y) :=
  Algebra.Homology.KernelAcyclic.HomologicalComplex.quasiIso_of_epi_of_kernel_acyclic
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainPlusComplex K Y)
    (topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic K Y)

end Cover

/-- On a paracompact Hausdorff space, ordinary cochains map quasi-isomorphically to global
sections of the double-plus singular-cochain complex. -/
theorem topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso
    {Y : TopCat.{0}} [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainPlusPlusComplex K Y) := by
  change QuasiIso
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainPlusComplex K Y ≫
      AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainPlusToPlusPlusComplex K Y)
  let := topOpenToGlobalSingularCochainPlusComplex_quasiIso K Y
  infer_instance

/-- On a paracompact Hausdorff space, ordinary coefficient singular cochains compute the global
section complex of the chosen singular-cochain sheaf resolution. -/
theorem topOpenToGlobalSingularCochainSheafComplex_quasiIso
    {Y : TopCat.{0}} [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex K Y) := by
  change QuasiIso
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainPlusPlusComplex K Y ≫
      (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainPlusPlusComplexIsoSheafComplex K Y).hom)
  let := topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso K (Y := Y)
  infer_instance

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Singular.SingularCoefficients
