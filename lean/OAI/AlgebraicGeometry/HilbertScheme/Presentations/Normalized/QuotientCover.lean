import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Quotient Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.QuotientCover.Grassmannian

noncomputable section

/-!
Every finite locally free quotient over a local ring is described by a
normalized matrix in a coordinate chart. The matrix kernel is exactly the
original submodule.
-/

open _root_.Module

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

def quotientBasisMatrix (N : Submodule R (ν → R)) (B : Basis ι R ((ν → R) ⧸ N)) :
    Matrix ι ν R := LinearMap.toMatrix' (B.equivFun.toLinearMap.comp N.mkQ)

theorem quotientBasisMatrix_normalized (N : Submodule R (ν → R))
    (a : ι → ν) (B : Basis ι R ((ν → R) ⧸ N))
    (hB : ∀ i, B i = N.mkQ (Pi.single (a i) 1)) :
    Matrices.Grassmannian.IsNormalized a (quotientBasisMatrix N B) := by
  ext i j
  change LinearMap.toMatrix' (B.equivFun.toLinearMap.comp N.mkQ) i (a j) = _
  rw [LinearMap.toMatrix'_apply, LinearMap.comp_apply, ← hB j]
  simp [Matrix.one_apply, eq_comm]

omit [DecidableEq ι] in
theorem quotientBasisMatrix_kernel (N : Submodule R (ν → R))
    (B : Basis ι R ((ν → R) ⧸ N)) : (Matrix.toLin' (quotientBasisMatrix N B)).ker = N := by
  rw [quotientBasisMatrix, Matrix.toLin'_toMatrix', LinearEquiv.ker_comp, N.ker_mkQ]

omit [DecidableEq ι] in
theorem local_quotient_basis_coordinates [IsLocalRing R]
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι)) :
    ∃ (a : ι → ν) (B : Basis ι R ((ν → R) ⧸ N.toSubmodule)),
      Function.Injective a ∧ ∀ i, B i = N.toSubmodule.mkQ (Pi.single (a i) 1) := by
  classical
  have : Module.FinitePresentation R ((ν → R) ⧸ N.toSubmodule) :=
    Module.finitePresentation_of_projective R ((ν → R) ⧸ N.toSubmodule)
  let v : ν → (ν → R) ⧸ N.toSubmodule := fun i => N.toSubmodule.mkQ ((Pi.basisFun R ν) i)
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    change Submodule.span R (Set.range (N.toSubmodule.mkQ ∘ Pi.basisFun R ν)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, (Pi.basisFun R ν).span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr N.toSubmodule.mkQ_surjective
  obtain ⟨κ, a, B, hB⟩ := Module.exists_basis_of_span_of_flat v hv
  have ha : Function.Injective a := by
    intro i j hij
    apply B.injective
    rw [hB i, hB j, hij]
  let : Module.Free R ((ν → R) ⧸ N.toSubmodule) := Module.Free.of_basis B
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hrank : Module.finrank R ((ν → R) ⧸ N.toSubmodule) = Fintype.card ι := by
    have h := N.rankAtStalk_eq ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
    simpa using h
  let e : κ ≃ ι := Fintype.equivOfCardEq ((Module.finrank_eq_card_basis B).symm.trans hrank)
  refine ⟨a ∘ e.symm, B.reindex e, ha.comp e.symm.injective, ?_⟩
  intro i
  simpa only [Basis.reindex_apply, Function.comp_apply, v, Pi.basisFun_apply] using hB (e.symm i)

/-- The normalized charts cover all Grassmannian quotients over local rings. -/
theorem normalizedGrassmannian_local_cover [IsLocalRing R]
    (N : Module.Grassmannian R (ν → R) (Fintype.card ι)) :
    ∃ (a : ι → ν) (Q : Matrix ι ν R) (hQ : Matrices.Grassmannian.IsNormalized a Q),
      Function.Injective a ∧ Quotients.Grassmannian.normalizedGrassmannian a Q hQ = N := by
  obtain ⟨a, B, ha, hB⟩ := local_quotient_basis_coordinates N
  refine ⟨a, quotientBasisMatrix N.toSubmodule B,
    quotientBasisMatrix_normalized N.toSubmodule a B hB, ha, ?_⟩
  apply Module.Grassmannian.ext
  exact quotientBasisMatrix_kernel N.toSubmodule B

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.QuotientCover.Grassmannian
