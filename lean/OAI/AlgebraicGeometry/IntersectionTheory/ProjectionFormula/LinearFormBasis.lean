import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousCoordinateMap
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Linear Form Basis -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis

noncomputable section

section

/-! The coordinate variables form the native basis of homogeneous
linear forms; independent partial coordinate systems extend to automorphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def coordinate (n : ℕ) (i : Fin (n + 1)) : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 :=
  ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩

def basis (n : ℕ) : Module.Basis (Fin (n + 1)) ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :=
  (Module.Basis.span (MvPolynomial.linearIndependent_X (R := ℂ) (σ := Fin (n + 1)))).map
    (LinearEquiv.ofEq _ _ MvPolynomial.homogeneousSubmodule_one_eq_span_X.symm)

theorem basis_apply (n : ℕ) (i : Fin (n + 1)) : basis n i = coordinate n i := by
  apply Subtype.ext
  simp only [basis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply, coordinate]

instance finite (n : ℕ) : Module.Finite ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) := Module.Finite.of_basis (basis n)

theorem dimension (n : ℕ) : Module.finrank ℂ (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) = n + 1 := by
  rw [Module.finrank_eq_card_basis (basis n), Fintype.card_fin]

theorem extend {n k : ℕ} (L : Fin k → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hL : LinearIndependent ℂ L)
    (ι : Fin k → Fin (n + 1)) (hι : Function.Injective ι) :
    ∃ e : (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) ≃ₗ[ℂ] (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1), ∀ i, e (coordinate n (ι i)) = L i := by
  let v := fun i => coordinate n (ι i)
  have hv : LinearIndependent ℂ v := by
    have h := (basis n).linearIndependent.comp ι hι
    simpa only [Function.comp_def, basis_apply] using h
  let b := Module.Basis.span hv
  let c := Module.Basis.span hL
  let f := b.equiv c (Equiv.refl (Fin k))
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e, fun i => ?_⟩
  have h := he (b i)
  have hf : f (b i) = c i := Module.Basis.equiv_apply b i c (Equiv.refl _)
  have he' := congrArg (fun a : Submodule.span ℂ (Set.range L) => (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)) hf
  rw [h] at he'
  simpa only [b, c, Module.Basis.coe_span_apply] using he'

end

/-! Linear maps on degree-one forms extend functorially to the
native graded homogeneous coordinate rings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GradedMap

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis

variable {n m l : ℕ}

def algebraHom (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) :
    Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n →ₐ[ℂ] Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m :=
  MvPolynomial.aeval (fun i => (F (coordinate n i)).val)

theorem algebraHom_X (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) (i : Fin (n + 1)) :
    algebraHom F (MvPolynomial.X i) = (F (coordinate n i)).val := MvPolynomial.aeval_X _ i

def gradedHom (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) :
    Foundations.Scheme.ProjectiveSpace.projectiveGrading n →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading m :=
  HomogeneousCoordinateMap.ofForms (fun i => (F (coordinate n i)).val) (fun i => (F (coordinate n i)).property)

theorem gradedHom_X (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) (i : Fin (n + 1)) :
    gradedHom F (MvPolynomial.X i) = (F (coordinate n i)).val :=
  HomogeneousCoordinateMap.ofForms_X _ _ i

def onForms (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) :
    Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 where
  toFun p := ⟨gradedHom F p.val, (gradedHom F).map_mem p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add (gradedHom F) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact (algebraHom F).toLinearMap.map_smul c p.val

theorem onForms_eq (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) : onForms F = F := by
  apply (basis n).ext
  intro i
  rw [basis_apply]
  apply Subtype.ext
  exact gradedHom_X F i

theorem on_form (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) (p : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    gradedHom F p.val = (F p).val :=
  congrArg Subtype.val (DFunLike.congr_fun (onForms_eq F) p)

theorem algebraHom_comp (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1)
    (G : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading l 1) :
    algebraHom (G.comp F) = (algebraHom G).comp (algebraHom F) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, algebraHom_X, LinearMap.comp_apply]
  exact (on_form G (F (coordinate n i))).symm

theorem gradedHom_comp (F : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1)
    (G : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading l 1) :
    gradedHom (G.comp F) = (gradedHom G).comp (gradedHom F) := by
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun (algebraHom_comp F G) p

theorem gradedHom_id : gradedHom (LinearMap.id : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) =
    GradedRingHom.id (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) := by
  have he : algebraHom (LinearMap.id : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) =
      AlgHom.id ℂ (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ i
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun he p

end GradedMap

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis
