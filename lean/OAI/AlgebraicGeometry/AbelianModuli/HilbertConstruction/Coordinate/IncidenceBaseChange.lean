import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SubmoduleExtension

/-! # Incidence Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.IncidenceBaseChange

noncomputable section

/-!
Containment of coordinate relations under a matrix survives coefficient
extension. A coefficient-ring isomorphism also reflects the condition.
-/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian

universe u v

variable {R A : Type u} [CommRing R] [CommRing A]
variable {ν μ : Type v} [Fintype ν] [DecidableEq ν]

theorem coordinateSubmoduleExtension_incidence (φ : R →+* A)
    (N : Submodule R (ν → R)) (M : Submodule R (μ → R)) (F : Matrix μ ν R)
    (h : N ≤ M.comap (Matrix.toLin' F)) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ N ≤
      (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ M).comap (Matrix.toLin' (F.map φ)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  have he : Matrix.toLin' (F.map φ) (φ ∘ x) = φ ∘ Matrix.toLin' F x := by
    ext i
    exact (RingHom.map_mulVec φ F x i).symm
  change Matrix.toLin' (F.map φ) (φ ∘ x) ∈ HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ M
  rw [he]
  exact Submodule.subset_span ⟨Matrix.toLin' F x, h hx, rfl⟩

theorem coordinateSubmoduleExtension_incidence_iff (e : R ≃+* A)
    (N : Submodule R (ν → R)) (M : Submodule R (μ → R)) (F : Matrix μ ν R) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension e.toRingHom N ≤
      (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension e.toRingHom M).comap (Matrix.toLin' (F.map e)) ↔
        N ≤ M.comap (Matrix.toLin' F) := by
  constructor
  · intro h
    have h' := coordinateSubmoduleExtension_incidence e.symm.toRingHom
      (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension e.toRingHom N)
      (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension e.toRingHom M) (F.map e) h
    rw [← HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp, ← HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_comp] at h'
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
      ext x
      exact e.symm_apply_apply x
    have hF : (F.map e).map e.symm.toRingHom = F := by
      ext i j
      exact e.symm_apply_apply _
    rw [he, HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_id, HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian.coordinateSubmoduleExtension_id, hF] at h'
    exact h'
  · exact coordinateSubmoduleExtension_incidence e.toRingHom N M F

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.IncidenceBaseChange
