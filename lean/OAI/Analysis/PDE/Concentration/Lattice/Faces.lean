import OAI.Analysis.PDE.Concentration.Parallelepiped

noncomputable section
namespace OAI.Analysis.PDE.Concentration

theorem linearPiola_add_period {m : ℕ}
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (F : (Fin m → ℝ) → (Fin m → ℝ)) (v : Fin m → ℝ)
    (hF : ∀ x, F (x + L v) = F x) (x : Fin m → ℝ) :
    linearPiola L F (x + v) = linearPiola L F x := by
  simp [linearPiola, Function.comp_def, map_add, hF]

theorem insertNth_eq_add_single {m : ℕ} (i : Fin (m + 1)) (a b : ℝ) (y : Fin m → ℝ) :
    (i.insertNth b y : Fin (m + 1) → ℝ) = i.insertNth a y + Pi.single i (b - a) := by
  have h := Fin.insertNth_sub_same (α := fun _ => ℝ) i b a y
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

/-- Periodicity on the actual lattice vector supplies the matching normal
flux and defining function on opposite parallelepiped faces. -/
theorem parallelepiped_face_match_of_periodic {m : ℕ}
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (F : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (r : (Fin (m + 1) → ℝ) → ℝ) (i : Fin (m + 1)) (a b : ℝ)
    (hF : ∀ x, F (x + L (Pi.single i (b - a))) = F x)
    (hr : ∀ x, r (x + L (Pi.single i (b - a))) = r x) (y : Fin m → ℝ) :
    r (L (i.insertNth b y)) = r (L (i.insertNth a y)) ∧
      linearPiola L F (i.insertNth b y) i = linearPiola L F (i.insertNth a y) i := by
  rw [insertNth_eq_add_single i a b y]
  exact ⟨by simpa only [map_add] using hr (L (i.insertNth a y)),
    congrFun (linearPiola_add_period L F _ hF _) i⟩

end OAI.Analysis.PDE.Concentration
