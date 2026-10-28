import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularLinearForm
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Changes -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.Changes.GradedHilbert

noncomputable section

/-!
Linear changes of homogeneous coordinates, extended from the degree-one
space to polynomial algebra automorphisms. These preserve the grading.
-/

open _root_.MvPolynomial _root_.Module

universe u

variable {K : Type u} [Field K] {n : ℕ}

def linearVariable (i : Fin (n + 1)) : Hilbert.Polynomial.GradedHilbert.grading K n 1 := ⟨X i, isHomogeneous_X K i⟩

def extendLinearMap (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 →ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) :
    Hilbert.Polynomial.GradedHilbert.CoordinateRing K n →ₐ[K] Hilbert.Polynomial.GradedHilbert.CoordinateRing K n :=
  aeval (fun i => (e (linearVariable i)).val)

theorem extendLinearMap_X (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 →ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) (i : Fin (n + 1)) :
    extendLinearMap e (X i) = (e (linearVariable i)).val := aeval_X _ _

theorem extendLinearMap_linear (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 →ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    (f : Hilbert.Polynomial.GradedHilbert.grading K n 1) : extendLinearMap e f.val = (e f).val := by
  classical
  have hf : f.val ∈ Submodule.span K (Set.range (X : Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact f.property
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
  have hcf : ∑ i, c i • linearVariable (K := K) i = f := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, linearVariable] using hc
  rw [← hcf]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (c i • ·) (extendLinearMap_X e i)

theorem extendLinearMap_comp (e f : Hilbert.Polynomial.GradedHilbert.grading K n 1 →ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) :
    extendLinearMap (e.comp f) = (extendLinearMap e).comp (extendLinearMap f) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, extendLinearMap_X, extendLinearMap_linear, LinearMap.comp_apply]

theorem extendLinearMap_id :
    extendLinearMap (LinearMap.id : Hilbert.Polynomial.GradedHilbert.grading K n 1 →ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) =
      AlgHom.id K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [extendLinearMap_X]
  rfl

def extendLinearEquiv (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1) :
    Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ≃ₐ[K] Hilbert.Polynomial.GradedHilbert.CoordinateRing K n :=
  AlgEquiv.ofAlgHom (extendLinearMap e.toLinearMap) (extendLinearMap e.symm.toLinearMap)
    (by
      rw [← extendLinearMap_comp]
      have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id :=
        LinearMap.ext fun x => e.apply_symm_apply x
      rw [h, extendLinearMap_id])
    (by
      rw [← extendLinearMap_comp]
      have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id :=
        LinearMap.ext fun x => e.symm_apply_apply x
      rw [h, extendLinearMap_id])

theorem extendLinearEquiv_homogeneous (e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1)
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d : ℕ} (hf : f.IsHomogeneous d) :
    (extendLinearEquiv e f).IsHomogeneous d := by
  change (eval₂ (algebraMap K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    (fun i => (e (linearVariable i)).val) f).IsHomogeneous d
  simpa only [one_mul] using hf.eval₂ (algebraMap K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    (fun i => (e (linearVariable i)).val) (fun c => isHomogeneous_C _ c)
    (fun i => (e (linearVariable i)).property)

theorem linearEquiv_sends_nonzero {V : Type*} [AddCommGroup V] [Module K V]
    (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) : ∃ e : V ≃ₗ[K] V, e v = w := by
  let ev := LinearEquiv.toSpanNonzeroSingleton K V v hv
  let ew := LinearEquiv.toSpanNonzeroSingleton K V w hw
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ev.symm.trans ew)
  refine ⟨e, ?_⟩
  have h := he (ev 1)
  change (ew (ev.symm (ev 1)) : V) = e (ev 1) at h
  rw [ev.symm_apply_apply] at h
  simpa only [ev, ew, LinearEquiv.toSpanNonzeroSingleton_apply, one_smul] using h.symm

theorem exists_coordinate_change (l : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hl : l.IsHomogeneous 1) (hl0 : l ≠ 0) :
    ∃ e : Hilbert.Polynomial.GradedHilbert.grading K n 1 ≃ₗ[K] Hilbert.Polynomial.GradedHilbert.grading K n 1, extendLinearEquiv e (X 0) = l := by
  have hv : linearVariable (K := K) (n := n) 0 ≠ 0 := by
    intro h
    exact X_ne_zero 0 (congrArg Subtype.val h)
  have hw : (⟨l, hl⟩ : Hilbert.Polynomial.GradedHilbert.grading K n 1) ≠ 0 := by
    intro h
    exact hl0 (congrArg Subtype.val h)
  obtain ⟨e, he⟩ := linearEquiv_sends_nonzero (K := K)
    (linearVariable 0) (⟨l, hl⟩ : Hilbert.Polynomial.GradedHilbert.grading K n 1) hv hw
  refine ⟨e, ?_⟩
  change extendLinearMap e.toLinearMap (X 0) = l
  rw [extendLinearMap_X]
  exact congrArg Subtype.val he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.Changes.GradedHilbert
