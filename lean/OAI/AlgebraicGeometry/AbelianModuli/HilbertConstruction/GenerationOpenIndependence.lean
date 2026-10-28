import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GenerationOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AffinePointDetection

/-! # Generation Open Independence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenerationOpenIndependence

noncomputable section

/-! Generation opens depend on the actual quotient relations, independently of normalized frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]

theorem normalizedKernel_incidence_baseChange {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (a : ι → ν) (b : κ → μ) (Q : Matrix ι ν R) (K : Matrix κ μ R)
    (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized b K) (F : Matrix μ ν R)
    (hF : (Matrix.toLin' Q).ker ≤ ((Matrix.toLin' K).ker).comap (Matrix.toLin' F)) :
    (Matrix.toLin' (Q.map φ)).ker ≤
      ((Matrix.toLin' (K.map φ)).ker).comap (Matrix.toLin' (F.map φ)) := by
  have h := Coordinate.IncidenceBaseChange.coordinateSubmoduleExtension_incidence φ _ _ F hF
  rw [HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ a Q hQ, HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ b K hK] at h
  exact h

omit [Fintype κ] [Fintype α] [DecidableEq ι] [DecidableEq κ] [DecidableEq α] in
theorem normalizedGenerationOpen_preimage {X Y : Scheme.{u}} (x : X ⟶ Y)
    (a : ι → ν) (b : κ → μ) (Q : Matrix ι ν Γ(Y, ⊤)) (F : α → Matrix μ ν Γ(Y, ⊤)) :
    x ⁻¹ᵁ Normalized.GenerationOpen.normalizedGenerationOpen a b Q F =
      Normalized.GenerationOpen.normalizedGenerationOpen a b (Q.map x.appTop.hom) (fun i => (F i).map x.appTop.hom) := by
  rw [Normalized.GenerationOpen.normalizedGenerationOpen, HilbertConstruction.Matrix.SurjectivityOpen.matrixSurjectiveOpen_preimage, Normalized.GenerationOpen.normalizedGenerationMatrix_map]
  rfl

theorem normalizedGenerationOpen_eq_of_kernels {X : Scheme.{u}}
    (a a' : ι → ν) (b b' : κ → μ)
    (Q Q' : Matrix ι ν Γ(X, ⊤)) (K K' : Matrix κ μ Γ(X, ⊤))
    (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (hQ' : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a' Q')
    (hK : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized b K) (hK' : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized b' K')
    (hq : (Matrix.toLin' Q).ker = (Matrix.toLin' Q').ker)
    (hk : (Matrix.toLin' K).ker = (Matrix.toLin' K').ker)
    (F : α → Matrix μ ν Γ(X, ⊤))
    (hF : ∀ i, (Matrix.toLin' Q).ker ≤ ((Matrix.toLin' K).ker).comap (Matrix.toLin' (F i))) :
    Normalized.GenerationOpen.normalizedGenerationOpen a b Q F = Normalized.GenerationOpen.normalizedGenerationOpen a' b' Q' F := by
  apply Open.AffinePointDetection.opens_eq_of_affine_range_iff
  intro R x
  let φ := (AffineProjective.Charts.affinePointCoefficients x).hom
  have hF' : ∀ i, (Matrix.toLin' Q').ker ≤ ((Matrix.toLin' K').ker).comap (Matrix.toLin' (F i)) := by
    rw [← hq, ← hk]
    exact hF
  rw [Normalized.GenerationOpen.normalizedGenerationOpen_affine_point a b Q K hQ hK F x
      (fun i => normalizedKernel_incidence_baseChange φ a b Q K hQ hK (F i) (hF i)),
    Normalized.GenerationOpen.normalizedGenerationOpen_affine_point a' b' Q' K' hQ' hK' F x
      (fun i => normalizedKernel_incidence_baseChange φ a' b' Q' K' hQ' hK' (F i) (hF' i))]
  have hqφ : (Matrix.toLin' (Q.map φ)).ker = (Matrix.toLin' (Q'.map φ)).ker := by
    rw [← HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ a Q hQ, ← HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ a' Q' hQ', hq]
  have hkφ : (Matrix.toLin' (K.map φ)).ker = (Matrix.toLin' (K'.map φ)).ker := by
    rw [← HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ b K hK, ← HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ b' K' hK', hk]
  change (Matrix.toLin' (K.map φ)).ker = _ ↔ (Matrix.toLin' (K'.map φ)).ker = _
  rw [hqφ, hkφ]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenerationOpenIndependence
