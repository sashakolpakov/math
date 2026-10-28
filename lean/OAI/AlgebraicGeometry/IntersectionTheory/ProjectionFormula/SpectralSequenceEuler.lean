import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ComplexEuler
import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-! # Spectral Sequence Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpectralSequenceEuler

noncomputable section

/-! A finitely supported spectral-sequence page of finite-length modules
has the same Euler characteristic on all later pages. Finiteness and support
are propagated through the actual page-homology isomorphisms. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength

variable (R : Type) [CommRing R] {ι : Type} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{0} R) c r₀)

theorem next_supported (F : Finset ι) (r : ℤ) (hr : r₀ ≤ r)
    (hout : ∀ i, i ∉ F → IsZero ((E.page r hr).X i)) :
    ∀ i, i ∉ F → IsZero ((E.page (r + 1) (by omega)).X i) := by
  intro i hi
  have h : IsZero ((E.page r hr).homology i) :=
    (HomologicalComplex.ExactAt.of_isZero (hout i hi)).isZero_homology
  exact h.of_iso (E.iso r (r + 1) i rfl hr).symm

theorem next_finite (F : Finset ι) (r : ℤ) (hr : r₀ ≤ r)
    (hlen : ∀ i ∈ F, Module.length R ((E.page r hr).X i) ≠ ⊤) :
    ∀ i ∈ F, Module.length R ((E.page (r + 1) (by omega)).X i) ≠ ⊤ := by
  intro i hi
  have h : Module.length R ((E.page r hr).homology i) ≠ ⊤ :=
    HomologyLength.homology_length_ne_top R ((E.page r hr).sc i) (hlen i hi)
  exact (E.iso r (r + 1) i rfl hr).toLinearEquiv.length_eq ▸ h

theorem next_euler (F : Finset ι) (r : ℤ) (hr : r₀ ≤ r)
    (hout : ∀ i, i ∉ F → IsZero ((E.page r hr).X i))
    (hlen : ∀ i ∈ F, Module.length R ((E.page r hr).X i) ≠ ⊤)
    (w : ι → ℚ) (hw : ∀ i j, (c r).Rel i j → w i + w j = 0) :
    (∑ i ∈ F, w i * ExactLength.rationalLength R ((E.page (r + 1) (by omega)).X i)) =
      ∑ i ∈ F, w i * ExactLength.rationalLength R ((E.page r hr).X i) := by
  calc
    _ = ∑ i ∈ F, w i * ExactLength.rationalLength R ((E.page r hr).homology i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun n : ℕ∞ => w i * (n.toNat : ℚ))
        (E.iso r (r + 1) i rfl hr).toLinearEquiv.length_eq.symm
    _ = _ := Finite.ComplexEuler.homology_euler R (E.page r hr) F hout hlen w hw

theorem page_property_congr (Q : (ι → ModuleCat.{0} R) → Prop)
    (r s : ℤ) (hr : r₀ ≤ r) (hs : r₀ ≤ s) (h : r = s) :
    Q (E.page r hr).X ↔ Q (E.page s hs).X := by
  subst s
  rfl

theorem later_pages (F : Finset ι)
    (hout : ∀ i, i ∉ F → IsZero ((E.page r₀).X i))
    (hlen : ∀ i ∈ F, Module.length R ((E.page r₀).X i) ≠ ⊤)
    (w : ι → ℚ) (hw : ∀ r, r₀ ≤ r → ∀ i j, (c r).Rel i j → w i + w j = 0)
    (n : ℕ) :
    (∀ i, i ∉ F → IsZero ((E.page (r₀ + n) (by omega)).X i)) ∧
      (∀ i ∈ F, Module.length R ((E.page (r₀ + n) (by omega)).X i) ≠ ⊤) ∧
      (∑ i ∈ F, w i * ExactLength.rationalLength R ((E.page (r₀ + n) (by omega)).X i)) =
        ∑ i ∈ F, w i * ExactLength.rationalLength R ((E.page r₀).X i) := by
  let Q : (ι → ModuleCat.{0} R) → Prop := fun M =>
    (∀ i, i ∉ F → IsZero (M i)) ∧
      (∀ i ∈ F, Module.length R (M i) ≠ ⊤) ∧
      (∑ i ∈ F, w i * ExactLength.rationalLength R (M i)) =
        ∑ i ∈ F, w i * ExactLength.rationalLength R ((E.page r₀).X i)
  change Q (E.page (r₀ + n) (by omega)).X
  induction n with
  | zero =>
    exact (page_property_congr R E Q _ r₀ (by omega) le_rfl (by omega)).mpr ⟨hout, hlen, rfl⟩
  | succ n ih =>
    have hr : r₀ ≤ r₀ + (n : ℤ) := by omega
    have ho := next_supported R E F (r₀ + n) hr ih.1
    have hl := next_finite R E F (r₀ + n) hr ih.2.1
    have he := (next_euler R E F (r₀ + n) hr ih.1 ih.2.1 w (hw _ hr)).trans ih.2.2
    exact (page_property_congr R E Q _ ((r₀ + n) + 1) (by omega) (by omega)
      (by omega)).mpr ⟨ho, hl, he⟩

def fromPage (r : ℤ) (hr : r₀ ≤ r) : SpectralSequence (ModuleCat.{0} R) c r where
  page s hs := E.page s (hr.trans hs)
  iso s t i hst hs := E.iso s t i hst (hr.trans hs)

theorem later_pages_from (r : ℤ) (hr : r₀ ≤ r) (F : Finset ι)
    (hout : ∀ i, i ∉ F → IsZero ((E.page r hr).X i))
    (hlen : ∀ i ∈ F, Module.length R ((E.page r hr).X i) ≠ ⊤)
    (w : ι → ℚ) (hw : ∀ s, r ≤ s → ∀ i j, (c s).Rel i j → w i + w j = 0)
    (n : ℕ) :
    (∀ i, i ∉ F → IsZero ((E.page (r + n) (by omega)).X i)) ∧
      (∀ i ∈ F, Module.length R ((E.page (r + n) (by omega)).X i) ≠ ⊤) ∧
      (∑ i ∈ F, w i * ExactLength.rationalLength R ((E.page (r + n) (by omega)).X i)) =
        ∑ i ∈ F, w i * ExactLength.rationalLength R ((E.page r hr).X i) :=
  later_pages R (fromPage R E r hr) F hout hlen w hw n

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpectralSequenceEuler
