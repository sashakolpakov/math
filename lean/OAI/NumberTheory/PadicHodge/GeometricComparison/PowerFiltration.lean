import OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationBounds
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityEquiv

/-! # Power Filtration -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PowerFiltration.FiltrationTransport

noncomputable section

/-! Pointwise filtrations and their exact decomposition into finite products. -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def power (I : Type*) (F : Linear.FiniteFiltration K V) : Linear.FiniteFiltration K (I → V) where
  step i := Submodule.pi Set.univ (fun _ => F.step i)
  antitone_step _ _ hij := Submodule.pi_mono (fun _ _ => F.antitone_step hij)
  eventually_top := by
    obtain ⟨a, ha⟩ := F.eventually_top
    exact ⟨a, by simp [ha]⟩
  eventually_bot := by
    obtain ⟨a, ha⟩ := F.eventually_bot
    exact ⟨a, by simp [ha]⟩

theorem mem_power {I : Type*} (F : Linear.FiniteFiltration K V) (i : ℤ) (x : I → V) :
    x ∈ (power I F).step i ↔ ∀ j, x j ∈ F.step i := by
  simp [power, Submodule.mem_pi]

theorem power_top (I : Type*) (F : Linear.FiniteFiltration K V) (i : ℤ) (hi : F.step i = ⊤) :
    (power I F).step i = ⊤ := by simp [power, hi]

theorem power_bot (I : Type*) (F : Linear.FiniteFiltration K V) (i : ℤ) (hi : F.step i = ⊥) :
    (power I F).step i = ⊥ := by simp [power, hi]

def powerSuccEquiv (n : ℕ) : (Fin (n + 1) → V) ≃ₗ[K] V × (Fin n → V) :=
  (LinearEquiv.piCongrLeft K (fun _ => V) (finSuccEquiv n)).trans (LinearEquiv.piOptionEquivProd K)

theorem powerSucc_step (n : ℕ) (F : Linear.FiniteFiltration K V) (i : ℤ) :
    ((power (Fin (n + 1)) F).step i).map (powerSuccEquiv (K := K) (V := V) n).toLinearMap =
      (ProductFiltration.FiltrationTransport.product F (power (Fin n) F)).step i := by
  ext x
  rw [Submodule.mem_map_equiv, mem_power]
  change (∀ j, ((powerSuccEquiv (K := K) (V := V) n).symm x) j ∈ F.step i) ↔
    x.1 ∈ F.step i ∧ x.2 ∈ (power (Fin n) F).step i
  rw [mem_power]
  constructor
  · intro h
    exact ⟨h 0, fun j => h j.succ⟩
  · rintro ⟨h₀, h⟩ j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact h₀
    · exact h k

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PowerFiltration.FiltrationTransport
