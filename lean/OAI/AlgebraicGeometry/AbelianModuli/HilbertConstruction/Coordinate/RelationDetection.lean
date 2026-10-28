import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.IncidenceBaseChange
import Mathlib.RingTheory.Grassmannian

/-! # Relation Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RelationDetection

noncomputable section

/-!
Coefficient maps that jointly detect zero also detect membership in a
coordinate submodule with projective quotient. A splitting supplies a matrix
whose kernel is exactly that submodule.
-/

universe u v w

variable {R : Type u} [CommRing R] {μ : Type v} [Fintype μ] [DecidableEq μ]

theorem projectiveQuotient_matrix_kernel (K : Submodule R (μ → R))
    [Module.Projective R ((μ → R) ⧸ K)] :
    ∃ H : Matrix μ μ R, (Matrix.toLin' H).ker = K := by
  obtain ⟨s, hs⟩ := K.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr K.mkQ_surjective)
  let L := s.comp K.mkQ
  refine ⟨LinearMap.toMatrix' L, ?_⟩
  rw [Matrix.toLin'_toMatrix']
  ext x
  constructor
  · intro hx
    have hz : s (K.mkQ x) = 0 := hx
    have he := LinearMap.congr_fun hs (K.mkQ x)
    change K.mkQ (s (K.mkQ x)) = K.mkQ x at he
    rw [hz, map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero K).mp he.symm
  · intro hx
    change s (K.mkQ x) = 0
    have hx0 : K.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hx
    rw [hx0, map_zero]

theorem coordinateRelation_of_jointly_detect_zero {α : Type w}
    (A : α → Type u) [∀ a, CommRing (A a)] (φ : ∀ a, R →+* A a)
    (hφ : ∀ r : R, (∀ a, φ a r = 0) → r = 0)
    (K : Submodule R (μ → R)) [Module.Projective R ((μ → R) ⧸ K)]
    (x : μ → R) (hx : ∀ a, φ a ∘ x ∈ HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (φ a) K) :
    x ∈ K := by
  obtain ⟨H, hH⟩ := projectiveQuotient_matrix_kernel K
  rw [← hH]
  change Matrix.toLin' H x = 0
  ext j
  apply hφ
  intro a
  have hxa := hx a
  rw [← hH] at hxa
  have hz := HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension_le_kernel (φ a) H hxa
  change Matrix.toLin' (H.map (φ a)) (φ a ∘ x) = 0 at hz
  exact (RingHom.map_mulVec (φ a) H x j).trans (congrFun hz j)

theorem coordinateIncidence_of_jointly_detect_zero {α : Type w}
    (A : α → Type u) [∀ a, CommRing (A a)] (φ : ∀ a, R →+* A a)
    (hφ : ∀ r : R, (∀ a, φ a r = 0) → r = 0)
    {ν : Type v} [Fintype ν] [DecidableEq ν]
    (N : Submodule R (ν → R)) (K : Submodule R (μ → R))
    [Module.Projective R ((μ → R) ⧸ K)] (F : Matrix μ ν R)
    (h : ∀ a, HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (φ a) N ≤
      (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (φ a) K).comap (Matrix.toLin' (F.map (φ a)))) :
    N ≤ K.comap (Matrix.toLin' F) := by
  intro x hx
  apply coordinateRelation_of_jointly_detect_zero A φ hφ K (Matrix.toLin' F x)
  intro a
  have he : φ a ∘ Matrix.toLin' F x = Matrix.toLin' (F.map (φ a)) (φ a ∘ x) := by
    ext j
    exact RingHom.map_mulVec (φ a) F x j
  rw [he]
  exact h a (Submodule.subset_span ⟨x, hx, rfl⟩)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.RelationDetection
