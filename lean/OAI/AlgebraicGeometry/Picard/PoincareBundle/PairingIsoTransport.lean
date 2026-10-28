import OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Pairing Iso Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PairingIsoTransport

noncomputable section

/-! Transport of all-test-scheme orthogonals through actual group-scheme isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal

variable {S : Scheme.{u}} {H K E : Over S} [GrpObj K] [GrpObj E]
  (e : ∀ T : Over S, (T ⟶ E) →* (T ⟶ E) →* Γ(T.left, ⊤)ˣ)
  (j : K ⟶ E) [IsMonHom j]

/-- Pull both arguments of the actual unit-valued pairing through the group morphism. -/
def pullPairing (T : Over S) : (T ⟶ K) →* (T ⟶ K) →* Γ(T.left, ⊤)ˣ :=
  ((MonoidHom.compHom' (P := Γ(T.left, ⊤)ˣ) (Kernel.Scheme.pointsMap j T)).comp
    (e T)).comp (Kernel.Scheme.pointsMap j T)

/-- Evaluation retains precisely the original two composed test points. -/
theorem pullPairing_apply {T : Over S} (x y : T ⟶ K) :
    pullPairing e j T x y = e T (x ≫ j) (y ≫ j) := rfl

/-- Orthogonality is transported on every test scheme and every further base change. -/
theorem orthogonal_iff (i : H ⟶ K) {T : Over S} (y : T ⟶ K) :
    y ∈ NaturalPairingOrthogonal.orthogonal i (pullPairing e j) T ↔ (y ≫ j) ∈ NaturalPairingOrthogonal.orthogonal (i ≫ j) e T := by
  constructor <;> intro h U a k
  · exact h U a k
  · exact h U a k

variable (d : K ≅ E) [IsMonHom d.hom]

/-- Inverse transport of an arbitrary ambient point preserves its complete orthogonality condition. -/
theorem orthogonal_inv_iff (i : H ⟶ K) {T : Over S} (y : T ⟶ E) :
    (y ≫ d.inv) ∈ NaturalPairingOrthogonal.orthogonal i (pullPairing e d.hom) T ↔ y ∈ NaturalPairingOrthogonal.orthogonal (i ≫ d.hom) e T := by
  rw [orthogonal_iff]
  simp only [Category.assoc, d.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PairingIsoTransport
