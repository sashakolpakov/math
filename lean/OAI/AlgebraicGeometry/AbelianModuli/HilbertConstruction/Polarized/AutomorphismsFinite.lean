import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismGraphPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedIsomorphismsFinite

/-! # Automorphisms Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismsFinite

noncomputable section

/-! Polarized full-level automorphisms over an algebraically closed field form a finite set, using the constructed common embedded graph Hilbert polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem polarizedAutomorphisms_finite_overAlgClosed : Finite (Moduli.Isomorphisms.LevelPreservingIso A A) := by
  let j := A.automorphismGraphPowerEmbedding.relativeMorphism A.graphBundle A.graphBundle
  let P := A.automorphismGraphPolynomial
  have : Finite {e : Moduli.Isomorphisms.LevelPreservingIso A A // Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P e.abelian.hom} :=
    Bounded.PolarizedIsomorphismsFinite.boundedPolarizedIsomorphisms_finite A A j P
  let q : Moduli.Isomorphisms.LevelPreservingIso A A → {e : Moduli.Isomorphisms.LevelPreservingIso A A // Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j P e.abelian.hom} :=
    fun e => ⟨e, A.automorphismGraphPolynomial_spec e⟩
  exact Finite.of_injective q (fun _ _ h => congrArg Subtype.val h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.AutomorphismsFinite
