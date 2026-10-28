import OAI.Analysis.PDE.Variational.CellL2
import OAI.Analysis.PDE.Variational.Completion

open Set _root_.MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Smooth tests vanish off the Dirichlet domain and respect the specified period vectors.
The periods impose no additional zero boundary condition on a fundamental cell. -/
def periodicTestSubmodule (Ω P : Set (CellCoordinates m)) :
    Submodule ℝ (CellCoordinates m → ℝ) where
  carrier := {u | ContDiff ℝ ∞ u ∧ (∀ x ∉ Ω, u x = 0) ∧
    ∀ p ∈ P, ∀ x, u (x + p) = u x}
  zero_mem' := ⟨contDiff_const, by simp, by simp⟩
  add_mem' := by
    intro u v hu hv
    exact ⟨hu.1.add hv.1, by intro x hx; simp [hu.2.1 x hx, hv.2.1 x hx],
      by intro p hp x; simp only [Pi.add_apply, hu.2.2 p hp, hv.2.2 p hp]⟩
  smul_mem' := by
    intro c u hu
    exact ⟨hu.1.const_smul c, by intro x hx; simp [hu.2.1 x hx],
      by intro p hp x; simp only [Pi.smul_apply, hu.2.2 p hp]⟩

abbrev PeriodicTests (Ω P : Set (CellCoordinates m)) := periodicTestSubmodule Ω P

theorem periodicTest_contDiff {Ω P : Set (CellCoordinates m)} (u : PeriodicTests Ω P) :
    ContDiff ℝ ∞ (u : CellCoordinates m → ℝ) := u.property.1

theorem periodicTest_contDiff_one {Ω P : Set (CellCoordinates m)} (u : PeriodicTests Ω P) :
    ContDiff ℝ 1 (u : CellCoordinates m → ℝ) := u.property.1.of_le (by norm_num)

def testValueMap (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m)) :
    PeriodicTests Ω P →ₗ[ℝ] Lp ℝ 2 (volume.restrict (Icc a b)) where
  toFun u := cellToL2 a b u (periodicTest_contDiff u).continuous
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def testGradientMap (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m)) :
    PeriodicTests Ω P →ₗ[ℝ] Lp (CellVectors m) 2 (volume.restrict (Icc a b)) where
  toFun u := cellToL2 a b (cellGradient u)
    (continuous_cellGradient (periodicTest_contDiff_one u))
  map_add' u v := by
    exact cellGradientToL2_add a b (periodicTest_contDiff_one u) (periodicTest_contDiff_one v)
  map_smul' c u := by
    exact cellGradientToL2_smul a b c (periodicTest_contDiff_one u)

theorem testValueMap_poincare (a b : CellCoordinates m) (hab : a ≤ b)
    (Ω P : Set (CellCoordinates m)) (j : Fin (m+1))
    (hface : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      j.insertNth (b j) y ∉ Ω) (u : PeriodicTests Ω P) :
    ‖testValueMap a b Ω P u‖ ≤ (2 * (b j-a j)) * ‖testGradientMap a b Ω P u‖ := by
  apply cell_poincare_gradient a b hab j (periodicTest_contDiff_one u)
  intro y hy
  exact u.property.2.1 _ (hface y hy)

/-- The zero-Dirichlet periodic energy space, realized as the closed space of actual L²
gradients of smooth periodic tests. -/
abbrev PeriodicH10 (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m)) :=
  GradientCompletion (testGradientMap a b Ω P)

def periodicTestEmbedding (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m)) :
    PeriodicTests Ω P →ₗ[ℝ] PeriodicH10 a b Ω P := testGradient (testGradientMap a b Ω P)

def periodicValue (a b : CellCoordinates m) (Ω P : Set (CellCoordinates m)) :
    PeriodicH10 a b Ω P →L[ℝ] Lp ℝ 2 (volume.restrict (Icc a b)) :=
  completedValue (testGradientMap a b Ω P) (testValueMap a b Ω P)

theorem periodicValue_test (a b : CellCoordinates m) (hab : a ≤ b)
    (Ω P : Set (CellCoordinates m)) (j : Fin (m+1))
    (hface : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      j.insertNth (b j) y ∉ Ω) (u : PeriodicTests Ω P) :
    periodicValue a b Ω P (periodicTestEmbedding a b Ω P u) = testValueMap a b Ω P u :=
  completedValue_testGradient _ _ (testValueMap_poincare a b hab Ω P j hface) u

theorem norm_periodicValue_le (a b : CellCoordinates m) (hab : a ≤ b)
    (Ω P : Set (CellCoordinates m)) (j : Fin (m+1))
    (hface : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      j.insertNth (b j) y ∉ Ω) (u : PeriodicH10 a b Ω P) :
    ‖periodicValue a b Ω P u‖ ≤ (2 * (b j-a j)) * ‖u‖ :=
  norm_completedValue_le _ _ (testValueMap_poincare a b hab Ω P j hface) u

theorem denseRange_periodicTestEmbedding (a b : CellCoordinates m)
    (Ω P : Set (CellCoordinates m)) : DenseRange (periodicTestEmbedding a b Ω P) :=
  denseRange_testGradient _

end OAI.Analysis.PDE.Variational
