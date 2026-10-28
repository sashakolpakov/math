import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRhamComplex
import OAI.AlgebraicGeometry.Comparison.Betti.DolbeaultRealization

/-! # Factorization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Factorization.Smooth

noncomputable section

/-! The actual algebraic cochain map factors through the independently defined holomorphic complex. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))
  (hc : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (φ a))

def holomorphicFormMap (n : ℕ) :
    Algebraic.Forms.Form A n →ₗ[ℂ] DeRhamComplex.forms E M n :=
  (FormPurity.Smooth.pureSmoothFormMap φ hφ hc n).codRestrict _ (DolbeaultRealization.Smooth.pureSmoothFormMap_dDoublePrime φ hφ hc n)

theorem holomorphicFormMap_d (n : ℕ) (a : Algebraic.Forms.Form A n) :
    DeRhamComplex.differential E M n (holomorphicFormMap φ hφ hc n a) =
      holomorphicFormMap φ hφ hc (n + 1) (Algebraic.Forms.differential A n a) := by
  apply Subtype.ext
  exact DolbeaultRealization.Smooth.pureSmoothFormMap_dPrime φ hφ hc n a

def holomorphicCochainMap :
    Algebraic.Forms.algebraicDeRhamComplex A ⟶ DeRhamComplex.complex E M :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (holomorphicFormMap φ hφ hc n)) (fun n => by
    rw [Algebraic.Forms.algebraicDeRhamComplex_d, DeRhamComplex.complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact holomorphicFormMap_d φ hφ hc n a)

theorem holomorphicCochainMap_factorization :
    holomorphicCochainMap φ hφ hc ≫ DeRhamComplex.inclusionCochainMap E M =
      Smooth.CochainMap.smoothCochainMap φ hφ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Factorization.Smooth
