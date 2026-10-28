import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.DirectSum.Decomposition

/-! # Basis Grading -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BasisGrading.GradedModules

noncomputable section

/-! A basis with assigned degrees gives an actual internal module decomposition. -/

open _root_.Module DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {ι : Type w} {δ : Type t} [DecidableEq δ]
variable (b : Basis ι R M) (w : ι → δ)

def basisPiece (d : δ) : Submodule R M := Submodule.span R (b '' {i | w i = d})

omit [DecidableEq δ] in
theorem basis_mem_piece (i : ι) : b i ∈ basisPiece b w (w i) :=
  Submodule.subset_span ⟨i, rfl, rfl⟩

def basisDecompose : M →ₗ[R] ⨁ d, basisPiece b w d :=
  b.constr R (fun i => DirectSum.lof R δ (fun d => basisPiece b w d) (w i)
    ⟨b i, basis_mem_piece b w i⟩)

theorem basisDecompose_basis (i : ι) :
    basisDecompose b w (b i) = DirectSum.lof R δ (fun d => basisPiece b w d) (w i)
      ⟨b i, basis_mem_piece b w i⟩ :=
  b.constr_basis R _ i

theorem basisDecompose_homogeneous (d : δ) (m : M) (hm : m ∈ basisPiece b w d) :
    basisDecompose b w m = DirectSum.lof R δ (fun d => basisPiece b w d) d ⟨m, hm⟩ := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨i, hi, rfl⟩ := hm
    subst d
    exact basisDecompose_basis b w i
  | zero =>
    rw [map_zero]
    exact (map_zero _).symm
  | add x y hx hy hx' hy' =>
    rw [map_add, hx', hy']
    exact (map_add (DirectSum.lof R δ (fun d => basisPiece b w d) d) ⟨x, hx⟩ ⟨y, hy⟩).symm
  | smul r x hx hx' =>
    rw [map_smul, hx']
    exact (map_smul (DirectSum.lof R δ (fun d => basisPiece b w d) d) r ⟨x, hx⟩).symm

theorem basisDecompose_left_inverse :
    (DirectSum.coeLinearMap (basisPiece b w)).comp (basisDecompose b w) = LinearMap.id := by
  apply b.ext
  intro i
  rw [LinearMap.comp_apply, basisDecompose_basis, DirectSum.coeLinearMap_lof]
  rfl

theorem basisDecompose_right_inverse :
    (basisDecompose b w).comp (DirectSum.coeLinearMap (basisPiece b w)) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro d
  apply LinearMap.ext
  intro x
  change basisDecompose b w (DirectSum.coeLinearMap (basisPiece b w)
    (DirectSum.lof R δ (fun d => basisPiece b w d) d x)) = _
  rw [DirectSum.coeLinearMap_lof, basisDecompose_homogeneous b w d x.val x.property]
  rfl

instance basisPieceDecomposition : DirectSum.Decomposition (basisPiece b w) :=
  DirectSum.Decomposition.ofLinearMap _ (basisDecompose b w)
    (basisDecompose_left_inverse b w) (basisDecompose_right_inverse b w)

omit [DecidableEq δ] in
theorem mem_basisPiece_iff (d : δ) (m : M) :
    m ∈ basisPiece b w d ↔ ∀ i, w i ≠ d → b.repr m i = 0 := by
  rw [basisPiece, b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h (Finsupp.mem_support_iff.mpr hn))
  · intro h i hi
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hi) (h i hn)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BasisGrading.GradedModules
