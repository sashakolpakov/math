import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorPage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.PageBounds

/-! # Iterated Tor Bounds -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorBounds

noncomputable section

/-! Bounded native resolutions give a finite supporting set for the
iterated Tor page, with lengths transported by its actual isomorphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

variable (R : Type) [CommRing R] (L M N : ModuleCat.{0} R)
  (P : ProjectiveResolution M) (Q : ProjectiveResolution L)

theorem supported (a b : ℕ)
    (hP : ∀ j, b < j → IsZero (P.complex.X j)) (hQ : ∀ i, a < i → IsZero (Q.complex.X i))
    (pq : ℤ × ℤ) (hpq : pq ∉ Tensor.PageBounds.support a b) :
    IsZero (((IteratedTorPage.spectralSequence R L M N P Q).page 3).X pq) := by
  let A := ChainToCochain.cochain R Q.complex
  let K := ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (ChainToCochain.cochain R P.complex)
  let : ∀ i, Module.Flat R (A.X i) := IteratedTorPage.flat_cochain_terms R L Q
  have hA : ∀ i, i < -(a : ℤ) ∨ 0 < i → IsZero (A.X i) :=
    ChainToCochain.bounded R Q.complex a hQ
  have hK : ∀ j, j < -(b : ℤ) ∨ 0 < j → IsZero (K.homology j) := by
    intro j hj
    apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    exact (tensorLeft N).map_isZero (ChainToCochain.bounded R P.complex b hP j hj)
  exact Tensor.PageBounds.supported R A K a b hA hK pq hpq

theorem finite (a b : ℕ)
    (h : ∀ i, i ≤ a → ∀ j, j ≤ b →
      Module.length R (((Tor (ModuleCat.{0} R) i).obj (((Tor (ModuleCat.{0} R) j).obj N).obj M)).obj L) ≠ ⊤)
    (pq : ℤ × ℤ) (hpq : pq ∈ Tensor.PageBounds.support a b) :
    Module.length R (((IteratedTorPage.spectralSequence R L M N P Q).page 3).X pq) ≠ ⊤ := by
  unfold Tensor.PageBounds.support at hpq
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hpq
  have hi := Finset.mem_range.mp (Finset.mem_product.mp hij).1
  have hj := Finset.mem_range.mp (Finset.mem_product.mp hij).2
  rw [(IteratedTorPage.iso R L M N P Q i j).toLinearEquiv.length_eq]
  exact h i (by omega) j (by omega)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorBounds
