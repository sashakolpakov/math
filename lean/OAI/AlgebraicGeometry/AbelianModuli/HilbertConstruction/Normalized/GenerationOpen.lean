import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GenerationCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityOpen

/-! # Generation Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GenerationOpen

noncomputable section

/-! The normalized relation-generation condition is represented by an explicit determinant-open subset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u} [Fintype ι] [Fintype ν]
variable [DecidableEq ν] [DecidableEq μ]

theorem normalizedGenerationMatrix_map {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (a : ι → ν) (b : κ → μ) (Q : Matrix ι ν R) (F : α → Matrix μ ν R) :
    (HilbertConstruction.Matrix.GeneratedImages.normalizedGenerationMatrix a b Q F).map φ =
      HilbertConstruction.Matrix.GeneratedImages.normalizedGenerationMatrix a b (Q.map φ) (fun i => (F i).map φ) := by
  ext j k
  cases k with
  | inl p =>
    have he : (F p.1 * HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix a Q).map φ =
        (F p.1).map φ * HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix a (Q.map φ) := by
      rw [Matrix.map_mul, HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.normalizedKernelMatrix_map]
    exact congrArg (fun H => H j p.2) he
  | inr l =>
    change φ ((1 : Matrix μ μ R) j (b l)) = (1 : Matrix μ μ A) j (b l)
    exact congrArg (fun H : Matrix μ μ A => H j (b l))
      (Matrix.map_one φ φ.map_zero φ.map_one)

variable [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α]

def normalizedGenerationOpen {X : Scheme.{u}} (a : ι → ν) (b : κ → μ)
    (Q : Matrix ι ν Γ(X, ⊤)) (F : α → Matrix μ ν Γ(X, ⊤)) : X.Opens :=
  HilbertConstruction.Matrix.SurjectivityOpen.matrixSurjectiveOpen (HilbertConstruction.Matrix.GeneratedImages.normalizedGenerationMatrix a b Q F)

theorem normalizedGenerationOpen_affine_point {X : Scheme.{u}} {R : CommRingCat.{u}}
    (a : ι → ν) (b : κ → μ) (Q : Matrix ι ν Γ(X, ⊤)) (K : Matrix κ μ Γ(X, ⊤))
    (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized b K) (F : α → Matrix μ ν Γ(X, ⊤))
    (x : Spec R ⟶ X)
    (hF : ∀ i, (Matrix.toLin' (Q.map (AffineProjective.Charts.affinePointCoefficients x).hom)).ker ≤
      ((Matrix.toLin' (K.map (AffineProjective.Charts.affinePointCoefficients x).hom)).ker).comap
        (Matrix.toLin' ((F i).map (AffineProjective.Charts.affinePointCoefficients x).hom))) :
    Set.range x ⊆ (normalizedGenerationOpen a b Q F : Set X) ↔
      (Matrix.toLin' (K.map (AffineProjective.Charts.affinePointCoefficients x).hom)).ker =
        ⨆ i, ((Matrix.toLin' (Q.map (AffineProjective.Charts.affinePointCoefficients x).hom)).ker).map
          (Matrix.toLin' ((F i).map (AffineProjective.Charts.affinePointCoefficients x).hom)) := by
  rw [normalizedGenerationOpen, HilbertConstruction.Matrix.SurjectivityOpen.matrixSurjectiveOpen_affine_point, normalizedGenerationMatrix_map]
  exact GenerationCriterion.normalizedGenerationMatrix_surjective_iff a b _ _
    (hQ.map (AffineProjective.Charts.affinePointCoefficients x).hom) (hK.map (AffineProjective.Charts.affinePointCoefficients x).hom) _ hF

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GenerationOpen
