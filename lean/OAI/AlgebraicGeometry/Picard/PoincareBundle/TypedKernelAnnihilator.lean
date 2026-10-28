import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRankAnnihilation

/-! # Typed Kernel Annihilator -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TypedKernelAnnihilator

/-! The full finite-flat degree in the actual polarization type annihilates its scheme-theoretic kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u

/-- The type degree kills all kernel points, including points over infinitesimal test schemes. -/
theorem killed_by_type_degree {k : Type u} [Field k] {a : ℕ}
    {A D : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D)
    (δ : Fin a → ℕ) (ht : f.HasPolarizationType δ)
    (T : Over (Spec (.of k))) (x : T ⟶ A.scheme) (hx : x ≫ f.hom = 1) : x ^ ((∏ i, δ i) ^ 2) = 1 := by
  let s : Spec (.of k) := ⟨⊥, inferInstance⟩
  have h := AbelianScheme.CartierDuality.IntrinsicRankAnnihilation.Construction.NormCharacters.kernel_killed_by_degree k f.hom s T x hx
  rwa [ht.degree] at h

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TypedKernelAnnihilator
