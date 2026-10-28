import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SecondPage
import Mathlib.Data.Finset.Prod

/-! # Page Bounds -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.PageBounds

noncomputable section

/-! Finite support of the iterated tensor page, obtained from the native
page computation and bounds on the complexes and their homology. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped Classical

variable (R : Type) [CommRing R] (A K : CochainComplex (ModuleCat.{0} R) ℤ)
  [∀ i, Module.Flat R (A.X i)]

def iso (p q : ℤ) :
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page 3).X (p, q) ≅
      (((tensorRight (K.homology (p + 2 * q + 1))).mapHomologicalComplex (.up ℤ)).obj A).homology (-(q + 1)) := by
  convert SecondPage.iso R A K (p - 2) (q - 1) (p + 2 * q + 1) (by omega) using 2 <;>
    congr 1 <;> omega

theorem zero_of_term (p q : ℤ) (h : IsZero (A.X (-(q + 1)))) :
    IsZero (((BrutalTensorSpectralSequence.spectralSequence R A K).page 3).X (p, q)) := by
  have hz := (tensorRight (K.homology (p + 2 * q + 1))).map_isZero h
  have hh : IsZero
      ((((tensorRight (K.homology (p + 2 * q + 1))).mapHomologicalComplex (.up ℤ)).obj A).homology (-(q + 1))) :=
    (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology
  exact hh.of_iso (iso R A K p q)

theorem zero_of_homology (p q : ℤ) (h : IsZero (K.homology (p + 2 * q + 1))) :
    IsZero (((BrutalTensorSpectralSequence.spectralSequence R A K).page 3).X (p, q)) := by
  have hz := (tensorLeft (A.X (-(q + 1)))).map_isZero h
  have hh : IsZero
      ((((tensorRight (K.homology (p + 2 * q + 1))).mapHomologicalComplex (.up ℤ)).obj A).homology (-(q + 1))) :=
    (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology
  exact hh.of_iso (iso R A K p q)

def support (a b : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.range (a + 1)).product (Finset.range (b + 1))).image
    (fun ij : ℕ × ℕ => (1 - 2 * (ij.1 : ℤ) - (ij.2 : ℤ), (ij.1 : ℤ) - 1))

theorem mem_support (a b : ℕ) (p q : ℤ) :
    (p, q) ∈ support a b ↔
      0 ≤ q + 1 ∧ q + 1 ≤ (a : ℤ) ∧ -(b : ℤ) ≤ p + 2 * q + 1 ∧ p + 2 * q + 1 ≤ 0 := by
  simp only [support, Finset.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨i, j, hij, hp, hq⟩
    have hi := Finset.mem_range.mp (Finset.mem_product.mp hij).1
    have hj := Finset.mem_range.mp (Finset.mem_product.mp hij).2
    omega
  · intro h
    exact ⟨(q + 1).toNat, (-(p + 2 * q + 1)).toNat,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
      by omega, by omega⟩

theorem supported (a b : ℕ)
    (hA : ∀ i, i < -(a : ℤ) ∨ 0 < i → IsZero (A.X i))
    (hK : ∀ j, j < -(b : ℤ) ∨ 0 < j → IsZero (K.homology j))
    (pq : ℤ × ℤ) (hpq : pq ∉ support a b) :
    IsZero (((BrutalTensorSpectralSequence.spectralSequence R A K).page 3).X pq) := by
  rcases pq with ⟨p, q⟩
  have ho : q + 1 < 0 ∨ (a : ℤ) < q + 1 ∨ p + 2 * q + 1 < -(b : ℤ) ∨ 0 < p + 2 * q + 1 := by
    by_contra hn
    apply hpq
    rw [mem_support]
    omega
  rcases ho with h | h | h | h
  · exact zero_of_term R A K p q (hA _ (Or.inr (by omega)))
  · exact zero_of_term R A K p q (hA _ (Or.inl (by omega)))
  · exact zero_of_homology R A K p q (hK _ (Or.inl h))
  · exact zero_of_homology R A K p q (hK _ (Or.inr h))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.PageBounds
