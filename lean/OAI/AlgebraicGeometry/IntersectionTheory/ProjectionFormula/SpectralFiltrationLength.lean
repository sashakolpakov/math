import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength
import Mathlib.Algebra.Homology.SpectralObject.Page
import Mathlib.Order.WithBotTop
import Mathlib.Data.ENat.BigOperators

/-! # Spectral Filtration Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpectralFiltrationLength

noncomputable section

/-! A finite filtration supplied by an actual spectral object has total
homology length equal to the sum of its graded lengths. The proof uses
the native short exact sequences of spectral opcycles. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.ComposableArrows
open scoped Classical

def point (a : ℤ) (d i : ℕ) : EInt := ((a + (min i d : ℕ) : ℤ) : EInt)

def lower (a : ℤ) (d i : ℕ) : point a d 0 ⟶ point a d i :=
  homOfLE (WithBotTop.coe_le_coe.mpr (by simp only [Nat.zero_min, Nat.cast_zero, add_zero]; omega))

def upper (a : ℤ) (d i : ℕ) : point a d i ⟶ point a d d :=
  homOfLE (WithBotTop.coe_le_coe.mpr (by simp only [min_self]; omega))

def step (a : ℤ) (d i : ℕ) : point a d i ⟶ point a d (i + 1) :=
  homOfLE (WithBotTop.coe_le_coe.mpr (by omega))

variable (R : Type) [CommRing R] (X : Abelian.SpectralObject (ModuleCat.{0} R) EInt)
  (a : ℤ) (d : ℕ) (n : ℤ)

def filtered (i : ℕ) : ModuleCat.{0} R := X.opcycles (lower a d i) (upper a d i) n

def graded (i : ℕ) : ModuleCat.{0} R :=
  X.E (lower a d i) (step a d i) (upper a d (i + 1)) (n - 1) n (n + 1)

def sequence (i : ℕ) : ShortComplex (ModuleCat.{0} R) :=
  X.shortComplexOpcyclesThreeδ₂Toδ₁ (lower a d i) (step a d i) (upper a d (i + 1))
    (lower a d (i + 1)) (upper a d i) (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    (n - 1) n (n + 1)

theorem shortExact (i : ℕ) : (sequence R X a d n i).ShortExact :=
  X.shortComplexOpcyclesThreeδ₂Toδ₁_shortExact _ _ _ _ _ _ _ _ _ _

theorem step_length (i : ℕ) :
    Module.length R (filtered R X a d n (i + 1)) =
      Module.length R (filtered R X a d n i) + Module.length R (graded R X a d n i) := by
  let S := sequence R X a d n i
  have hS : S.ShortExact := shortExact R X a d n i
  exact Module.length_eq_add_of_exact S.f.hom S.g.hom
    ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
    ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)

theorem initial_zero : IsZero (filtered R X a d n 0) := by
  apply X.isZero_opcycles
  apply X.isZero_H_obj_of_isIso
  have h : lower a d 0 = 𝟙 (point a d 0) := Subsingleton.elim _ _
  rw [h]
  infer_instance

def endpointIso : filtered R X a d n d ≅ (X.H n).obj (mk₁ (lower a d d)) := by
  change X.opcycles (lower a d d) (upper a d d) n ≅ _
  have h : upper a d d = 𝟙 (point a d d) := Subsingleton.elim _ _
  rw [h]
  exact X.opcyclesIsoH (lower a d d) (n - 1) n

theorem filtered_length (i : ℕ) :
    Module.length R (filtered R X a d n i) =
      ∑ j ∈ Finset.range i, Module.length R (graded R X a d n j) := by
  induction i with
  | zero =>
    let := ModuleCat.subsingleton_of_isZero (initial_zero R X a d n)
    simp only [Finset.range_zero, Finset.sum_empty, Module.length_eq_zero]
  | succ i ih =>
    rw [show i + 1 = Nat.succ i from rfl] at *
    rw [step_length, ih, Finset.sum_range_succ]

theorem length_eq_sum :
    Module.length R ((X.H n).obj (mk₁ (lower a d d))) =
      ∑ i ∈ Finset.range d, Module.length R (graded R X a d n i) := by
  rw [← (endpointIso R X a d n).toLinearEquiv.length_eq]
  exact filtered_length R X a d n d

theorem finite_length (h : ∀ i ∈ Finset.range d, Module.length R (graded R X a d n i) ≠ ⊤) :
    Module.length R ((X.H n).obj (mk₁ (lower a d d))) ≠ ⊤ := by
  rw [length_eq_sum, ENat.sum_ne_top]
  exact h

theorem rationalLength_eq_sum
    (h : ∀ i ∈ Finset.range d, Module.length R (graded R X a d n i) ≠ ⊤) :
    ExactLength.rationalLength R ((X.H n).obj (mk₁ (lower a d d))) =
      ∑ i ∈ Finset.range d, ExactLength.rationalLength R (graded R X a d n i) := by
  simp only [ExactLength.rationalLength]
  rw [length_eq_sum, ENat.toNat_sum h, Nat.cast_sum]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpectralFiltrationLength
