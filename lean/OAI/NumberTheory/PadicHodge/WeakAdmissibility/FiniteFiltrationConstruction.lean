import OAI.NumberTheory.PadicHodge.WeakAdmissibility.FilteredRepresentations

/-! # Finite Filtration Construction -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFiltrationConstruction

noncomputable section

/-! A finite filtration obtained from exhaustive and separated geometric steps. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.FilteredRepresentations.Construction
variable {K D : Type*} [Field K] [AddCommGroup D] [Module K D] [Module.Finite K D]

theorem exhaustive_eventually_top (F : ℤ → Submodule K D) (hF : Antitone F)
    (hEx : ∀ x : D, ∃ i : ℤ, x ∈ F i) : ∃ a : ℤ, F a = ⊤ := by
  let f : ℕ →o Submodule K D := ⟨fun n => F (-(n : ℤ)), fun _ _ h => hF (by omega)⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian K D) f
  refine ⟨-(n : ℤ), top_unique (fun x _ => ?_)⟩
  obtain ⟨i, hi⟩ := hEx x
  let m := max n (-i).toNat
  have hnm : n ≤ m := le_max_left _ _
  have hmi : -(m : ℤ) ≤ i := by dsimp only [m]; omega
  have he : F (-(n : ℤ)) = F (-(m : ℤ)) := hn m hnm
  rw [he]
  exact hF hmi hi

theorem separated_eventually_bot (F : ℤ → Submodule K D) (hF : Antitone F)
    (hSep : ∀ x : D, (∀ i : ℤ, x ∈ F i) → x = 0) : ∃ b : ℤ, F b = ⊥ := by
  let f : ℕ →o (Submodule K D)ᵒᵈ := ⟨fun n => F (n : ℤ), fun _ _ h => hF (by omega)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨n, bot_unique (fun x hx => ?_)⟩
  apply (Submodule.mem_bot K).mpr
  apply hSep x
  intro i
  let m := max n i.toNat
  have hnm : n ≤ m := le_max_left _ _
  have him : i ≤ (m : ℤ) := by dsimp only [m]; omega
  have he : F (n : ℤ) = F (m : ℤ) := hn m hnm
  exact hF him (he ▸ hx)

def ofExhaustiveSeparated (F : ℤ → Submodule K D) (hF : Antitone F)
    (hEx : ∀ x : D, ∃ i : ℤ, x ∈ F i)
    (hSep : ∀ x : D, (∀ i : ℤ, x ∈ F i) → x = 0) : FilteredRepresentations.Construction.FiniteFiltration K D where
  step := F
  antitone_step := hF
  eventually_top := exhaustive_eventually_top F hF hEx
  eventually_bot := separated_eventually_bot F hF hSep

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFiltrationConstruction
