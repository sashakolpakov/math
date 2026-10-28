import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjective
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.CharZero.Infinite

/-! # Affine Neighborhood -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.AffineNeighborhood

noncomputable section

/-! Every finite set of points in a complex projective presentation has a
common affine neighborhood. A linear homogeneous polynomial avoiding all
the point ideals is obtained by finite subspace avoidance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe v

theorem exists_linear_form (n : ℕ) {ι : Type v} [Finite ι]
    (x : ι → Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    ∃ f : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n, f ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ∧
      ∀ i, f ∉ (x i).asHomogeneousIdeal := by
  let V := Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1
  let N : ι → Submodule ℂ V := fun i =>
    ((x i).asHomogeneousIdeal.toIdeal.restrictScalars ℂ).comap V.subtype
  have hN (i : ι) : N i ≠ ⊤ := by
    obtain ⟨k, hk⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen n (x i)
    rw [Foundations.Scheme.ProjectiveCoordinateCover.mem_projectiveCoordinateOpen] at hk
    intro h
    have hm : (⟨MvPolynomial.X k, MvPolynomial.isHomogeneous_X ℂ k⟩ : V) ∈ N i := by
      rw [h]
      trivial
    exact hk hm
  obtain ⟨f, hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top N hN
  exact ⟨f, f.property, hf⟩

theorem projectiveSpace_common_affine (n : ℕ) {ι : Type v} [Finite ι]
    (x : ι → Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    ∃ U : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨f, hf, hx⟩ := exists_linear_form n x
  exact ⟨Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) f,
    Proj.isAffineOpen_basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) f hf (by decide : 0 < 1),
    fun i => (Proj.mem_basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) f (x i)).mpr (hx i)⟩

theorem common_affine {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) {ι : Type v} [Finite ι] (x : ι → X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U := by
  obtain ⟨U, hU, hx⟩ := projectiveSpace_common_affine P.ambientDimension (fun i => P.embedding (x i))
  exact ⟨P.embedding ⁻¹ᵁ U, hU.preimage P.embedding, hx⟩

theorem common_affine_finset {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) (s : Finset X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ s, x ∈ U := by
  obtain ⟨U, hU, hx⟩ := common_affine P (fun x : s => x.val)
  exact ⟨U, hU, fun x hx' => hx ⟨x, hx'⟩⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.AffineNeighborhood
