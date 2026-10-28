import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorTo
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Sector Sum -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorSum.Dolbeault

noncomputable section

section

/-! Finite sector sums and their holomorphic coordinate regrouping. -/

open _root_.TopologicalSpace Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentSectorSum (s : Finset ι) (A : Finset ι → (ι → ℂ) → ℂ) (x : ι → ℂ) : ℂ :=
  ∑ J ∈ s.powerset, A J (SectorTo.Dolbeault.laurentInverseCoordinates J x)

theorem laurentSectorSum_differentiableOn (s : Finset ι) (A : Finset ι → (ι → ℂ) → ℂ)
    (hA : ∀ J ∈ s.powerset, Differentiable ℂ (A J)) :
    DifferentiableOn ℂ (laurentSectorSum s A) (SectorTo.Dolbeault.laurentCoordinateDomain s) := by
  apply DifferentiableOn.fun_sum
  intro J hJ
  exact (hA J hJ).differentiableOn.comp
    (SectorTo.Dolbeault.laurentInverseCoordinates_differentiableOn s J (Finset.mem_powerset.mp hJ))
    (fun _ _ => Set.mem_univ _)

omit [Fintype ι] in
theorem laurentSectorSum_insert (s : Finset ι) (i : ι) (hi : i ∉ s)
    (A : Finset ι → (ι → ℂ) → ℂ) (x : ι → ℂ) :
    laurentSectorSum (insert i s) A x = laurentSectorSum s A x +
      laurentSectorSum s (fun J => A (insert i J)) (Function.update x i (x i)⁻¹) := by
  unfold laurentSectorSum
  rw [Finset.sum_powerset_insert hi]
  apply congrArg (_ + ·)
  apply Finset.sum_congr rfl
  intro J hJ
  have hiJ : i ∉ J := fun hj => hi (Finset.mem_powerset.mp hJ hj)
  rw [SectorTo.Dolbeault.laurentInverseCoordinates_insert J i hiJ]

omit [Fintype ι] in
theorem laurentSectorSum_vanishes (s : Finset ι) (i : ι) (hi : i ∉ s)
    (A : Finset ι → (ι → ℂ) → ℂ)
    (hA : ∀ J ∈ s.powerset, ∀ x : ι → ℂ, x i = 0 → A J x = 0)
    (x : ι → ℂ) (hx : x i = 0) : laurentSectorSum s A x = 0 := by
  apply Finset.sum_eq_zero
  intro J hJ
  apply hA J hJ
  have hiJ : i ∉ J := fun hj => hi (Finset.mem_powerset.mp hJ hj)
  simpa only [SectorTo.Dolbeault.laurentInverseCoordinates, ite_eq_right hiJ] using hx

end

section

/-! The actual linear assembly map from normalized entire sector coefficients. -/

open _root_.TopologicalSpace Set
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentEntireFunction (a : Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ))) (x : ι → ℂ) : ℂ :=
  a.val ⟨x, trivial⟩

omit [DecidableEq ι] in
theorem laurentEntireFunction_differentiable (a : Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ))) :
    Differentiable ℂ (laurentEntireFunction a) := by
  have he : FiberVanishing.Dolbeault.holomorphicFunctionExtension ⊤ a = laurentEntireFunction a :=
    funext (fun x => Holomorphic.CoefficientMem.openCoefficientExtension_apply ⊤ a.val ⟨x, trivial⟩)
  rw [← he]
  exact differentiableOn_univ.mp (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable ⊤ a)

def laurentSectorSectionFamilies (s : Finset ι) :
    Submodule ℂ (Finset ι → Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ))) where
  carrier := {A | (∀ J, A J ∈ SectorTo.Dolbeault.laurentSectorCoefficients J) ∧ (∀ J, ¬J ⊆ s → A J = 0)}
  zero_mem' := ⟨fun J => (SectorTo.Dolbeault.laurentSectorCoefficients J).zero_mem, fun _ _ => rfl⟩
  add_mem' := by
    intro A B hA hB
    refine ⟨fun J => (SectorTo.Dolbeault.laurentSectorCoefficients J).add_mem (hA.1 J) (hB.1 J), ?_⟩
    intro J hJ
    change A J + B J = 0
    rw [hA.2 J hJ, hB.2 J hJ, add_zero]
  smul_mem' := by
    intro c A hA
    refine ⟨fun J => (SectorTo.Dolbeault.laurentSectorCoefficients J).smul_mem c (hA.1 J), ?_⟩
    intro J hJ
    change c • A J = 0
    rw [hA.2 J hJ, smul_zero]

def laurentSectorAssembly (s : Finset ι) (A : laurentSectorSectionFamilies s) :
    Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s) :=
  PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable _
    (laurentSectorSum s (fun J => laurentEntireFunction (A.val J)))
    (laurentSectorSum_differentiableOn s _ (fun J _ => laurentEntireFunction_differentiable (A.val J)))

theorem laurentSectorAssembly_apply (s : Finset ι) (A : laurentSectorSectionFamilies s)
    (x : SectorTo.Dolbeault.laurentCoordinateDomain s) :
    (laurentSectorAssembly s A).val x =
      ∑ J ∈ s.powerset, (A.val J).val ⟨SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩ := rfl

def laurentSectorAssemblyMap (s : Finset ι) :
    laurentSectorSectionFamilies s →ₗ[ℂ] Holomorphic.FunctionPure.holomorphicFunctions (SectorTo.Dolbeault.laurentCoordinateDomain s) where
  toFun := laurentSectorAssembly s
  map_add' A B := by
    apply Subtype.ext
    funext x
    change (∑ J ∈ s.powerset,
      ((A.val J).val ⟨SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩ +
        (B.val J).val ⟨SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩)) = _
    exact Finset.sum_add_distrib
  map_smul' c A := by
    apply Subtype.ext
    funext x
    change (∑ J ∈ s.powerset, c • (A.val J).val ⟨SectorTo.Dolbeault.laurentInverseCoordinates J x.val, trivial⟩) = _
    exact Finset.smul_sum.symm

end

/-! A smooth homogeneous function is determined by one diagonal iterated derivative. -/

open _root_.TopologicalSpace
open scoped ContDiff

theorem continuous_homogeneous_radial {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (hf : Continuous f) (n : ℕ)
    (hscale : ∀ c : ℂ, c ≠ 0 → ∀ x, f (c • x) = c ^ n * f x) (x : E) :
    (fun c : ℂ => f (c • x)) = fun c => c ^ n * f x := by
  apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (hf.comp (continuous_id.smul continuous_const))
    ((continuous_id.pow n).mul continuous_const)
  intro c hc
  exact hscale c hc x

theorem homogeneousFunction_diagonalDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (hf : ContDiff ℂ ∞ f) (n : ℕ)
    (hscale : ∀ c : ℂ, c ≠ 0 → ∀ x, f (c • x) = c ^ n * f x) (x : E) :
    iteratedFDeriv ℂ n f 0 (fun _ => x) = (n.factorial : ℂ) * f x := by
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight x
  have hcomp := L.iteratedFDeriv_comp_right hf 0 (i := n) (WithTop.coe_le_coe.mpr le_top)
  have he : iteratedDeriv n (fun c : ℂ => f (c • x)) 0 =
      iteratedFDeriv ℂ n f 0 (fun _ => x) := by
    change iteratedDeriv n (f ∘ L) 0 = _
    rw [iteratedDeriv_eq_iteratedFDeriv, hcomp]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, zero_smul, one_smul]
  have h := congrArg (fun g : ℂ → ℂ => iteratedDeriv n g 0)
    (continuous_homogeneous_radial f hf.continuous n hscale x)
  rw [he, iteratedDeriv_mul_const_field, iteratedDeriv_pow, Nat.descFactorial_self,
    Nat.sub_self, pow_zero, mul_one] at h
  exact h

theorem laurentEntireFunction_contDiff {ι : Type} [Fintype ι]
    (a : Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ))) :
    ContDiff ℂ ∞ (laurentEntireFunction a) := by
  have ha : ContDiffOn ℂ ∞ (Holomorphic.CoefficientMem.openCoefficientExtension ⊤ a.val) Set.univ := a.property
  have he : Holomorphic.CoefficientMem.openCoefficientExtension ⊤ a.val = laurentEntireFunction a :=
    funext (fun x => Holomorphic.CoefficientMem.openCoefficientExtension_apply ⊤ a.val ⟨x, trivial⟩)
  exact he ▸ contDiffOn_univ.mp ha

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorSum.Dolbeault
