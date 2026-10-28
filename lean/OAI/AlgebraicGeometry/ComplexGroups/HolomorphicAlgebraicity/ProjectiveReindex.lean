import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSubscheme
import Mathlib.LinearAlgebra.Pi

/-! # Projective Reindex -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveReindex.Constructions.Algebraization

noncomputable section

/-!
# Relabeling finite projective coordinates for the scheme construction
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

def reindexProjective {ι κ : Type*} (e : ι ≃ κ) :
    Projectivization ℂ (ι → ℂ) → Projectivization ℂ (κ → ℂ) :=
  Projectivization.map (LinearEquiv.piCongrLeft' ℂ (fun _ : ι => ℂ) e).toLinearMap
    (LinearEquiv.piCongrLeft' ℂ (fun _ : ι => ℂ) e).injective

theorem reindexProjective_injective {ι κ : Type*} (e : ι ≃ κ) :
    Function.Injective (reindexProjective e) :=
  Projectivization.map_injective _ _

theorem reindexProjective_surjective {ι κ : Type*} (e : ι ≃ κ) :
    Function.Surjective (reindexProjective e) := by
  intro p
  refine ⟨reindexProjective e.symm p, ?_⟩
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [reindexProjective, Projectivization.map_mk]
    congr 1
    ext j
    exact congrArg v (e.apply_symm_apply j)

theorem mem_projectiveCommonZeroLocus_reindex
    {ι κ α : Type*} (e : ι ≃ κ) (f : α → MvPolynomial ι ℂ)
    (degree : α → ℕ) (hf : ∀ a, (f a).IsHomogeneous (degree a))
    (p : Projectivization ℂ (ι → ℂ)) :
    reindexProjective e p ∈ Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus
      (fun a => MvPolynomial.rename e (f a)) degree (fun a => (hf a).rename_isHomogeneous) ↔
      p ∈ Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus f degree hf := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [reindexProjective, Projectivization.map_mk, Foundations.Scheme.ProjectiveZeroLocus.mem_projectiveCommonZeroLocus_mk,
      MvPolynomial.eval_rename]
    have he : (fun i => (LinearEquiv.piCongrLeft' ℂ (fun _ : ι => ℂ) e) v (e i)) = v := by
      ext i
      exact congrArg v (e.symm_apply_apply i)
    change (∀ a, MvPolynomial.eval (fun i => (LinearEquiv.piCongrLeft' ℂ
      (fun _ : ι => ℂ) e) v (e i)) (f a) = 0) ↔ _
    rw [he]

theorem exists_reduced_projective_subscheme_finite_coordinates
    {ι α : Type*} [Fintype ι] [Nonempty ι]
    (f : α → MvPolynomial ι ℂ) (degree : α → ℕ)
    (hf : ∀ a, (f a).IsHomogeneous (degree a)) :
    ∃ (n : ℕ) (e : ι ≃ Fin (n + 1))
      (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (i : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)),
      IsReduced X.left ∧ IsClosedImmersion i.left ∧ IsProper X.hom ∧
      ∀ p : Projectivization ℂ (ι → ℂ),
        Foundations.Scheme.ProjectiveComplexPoints.projectiveComplexPointsEquiv n (reindexProjective e p) ∈ range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ↔
          p ∈ Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus f degree hf := by
  let n := Fintype.card ι - 1
  have hc : Fintype.card ι = n + 1 := by
    have hpos := Fintype.card_pos (α := ι)
    dsimp [n]
    omega
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hc)
  obtain ⟨X, i, hX, hi, hp, heq⟩ := ProjectiveSubscheme.Constructions.Algebraization.exists_reduced_projective_subscheme_of_equations
    (fun a => MvPolynomial.rename e (f a)) degree (fun a => (hf a).rename_isHomogeneous)
  refine ⟨n, e, X, i, hX, hi, hp, fun p => ?_⟩
  rw [heq]
  exact mem_projectiveCommonZeroLocus_reindex e f degree hf p

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveReindex.Constructions.Algebraization
