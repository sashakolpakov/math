import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Hecke -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Hecke.Construction

noncomputable section

/-!
CentralAction concerns the geometric representation of the Hecke algebra, not
finite order in the spherical algebra itself. This file proves the
distinction for the actual central element with multiplier q. Thus a
geometric scalar-descent identification cannot be replaced by an
arbitrary algebra representation when repairing the target interface.
This is not a counterexample to the manuscript's geometric assertion.
-/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

section Group

variable {G : Type*} [Group G] (U : Subgroup G)

/-- A central raw operator can have a trivial positive power only when
the corresponding group element has that power in the integral level. -/
theorem central_power_one_requires_level
    (z : G) (hz : ∀ g : G, Commute g z) (n : ℕ)
    (hp : (TateComparison.HeckeKernel.centralHeckeUnit U z hz).val ^ n = 1) : z ^ n ∈ U := by
  let tr : G →* Module.End ℚ (TateComparison.HeckeKernel.CosetModule U) := {
    toFun := TateComparison.HeckeKernel.translate U
    map_one' := TateComparison.HeckeKernel.translate_one U
    map_mul' := TateComparison.HeckeKernel.translate_mul U }
  have ht : TateComparison.HeckeKernel.translate U (z⁻¹ ^ n) = 1 := by
    change tr (z⁻¹ ^ n) = 1
    rw [map_pow]
    exact congrArg (fun h : TateComparison.HeckeKernel.SphericalHecke U => h.val) hp
  have hc := congrArg (fun f : Module.End ℚ (TateComparison.HeckeKernel.CosetModule U) =>
    f (Finsupp.single (QuotientGroup.mk (1 : G)) 1)) ht
  have hsingle : Finsupp.single (QuotientGroup.mk (z⁻¹ ^ n) : G ⧸ U) (1 : ℚ) =
      Finsupp.single (QuotientGroup.mk (1 : G)) 1 := by
    simpa [TateComparison.HeckeKernel.translate] using hc
  have heq := Finsupp.single_left_injective (by norm_num : (1 : ℚ) ≠ 0) hsingle
  have hmem := QuotientGroup.eq.mp heq
  simpa using hmem

end Group

variable (s q : ℕ) [Fact q.Prime]

/-- Blockwise scalar exponents, with multiplier exponent one, as for C0. -/
def c0Representative (a : Fin s → ℤ) : TateComparison.HeckeKernel.SplitGroup s q :=
  (fun v => Matrix.GeneralLinearGroup.scalar (Fin 3) (TateComparison.HeckeKernel.qUnit q ^ a v), TateComparison.HeckeKernel.qUnit q)

theorem c0Representative_commutes (a : Fin s → ℤ) (g : TateComparison.HeckeKernel.SplitGroup s q) :
    Commute g (c0Representative s q a) := by
  change g * c0Representative s q a = c0Representative s q a * g
  apply Prod.ext
  · funext v
    exact (Matrix.GeneralLinearGroup.scalar_commute (TateComparison.HeckeKernel.qUnit q ^ a v) (g.1 v)).symm
  · exact mul_comm _ _

/-- The multiplier of an integral-level element is a q-adic unit. -/
theorem integralLevel_multiplier_norm_one
    (g : TateComparison.HeckeKernel.SplitGroup s q) (hg : g ∈ TateComparison.HeckeKernel.integralLevel s q) : ‖(g.2 : ℚ_[q])‖ = 1 := by
  obtain ⟨u, rfl⟩ := hg
  change ‖((u.2 : ℤ_[q]) : ℚ_[q])‖ = 1
  exact PadicInt.norm_units u.2

/-- C0 has infinite order in the actual spherical algebra. Finite order
must therefore be proved in its specified geometric action. -/
theorem c0_not_finite_order_in_spherical_algebra (a : Fin s → ℤ) :
    ¬ ∃ n : ℕ, 0 < n ∧
      (TateComparison.HeckeKernel.centralHeckeUnit (TateComparison.HeckeKernel.integralLevel s q) (c0Representative s q a)
        (c0Representative_commutes s q a)).val ^ n = 1 := by
  rintro ⟨n, hn, hp⟩
  have hmem := central_power_one_requires_level (TateComparison.HeckeKernel.integralLevel s q)
    (c0Representative s q a) (c0Representative_commutes s q a) n hp
  have hnorm := integralLevel_multiplier_norm_one s q
    (c0Representative s q a ^ n) hmem
  change ‖(q : ℚ_[q]) ^ n‖ = 1 at hnorm
  rw [norm_pow] at hnorm
  have hlt : ‖(q : ℚ_[q])‖ ^ n < 1 :=
    pow_lt_one₀ (norm_nonneg _) Padic.norm_p_lt_one (Nat.ne_zero_of_lt hn)
  exact (ne_of_lt hlt) hnorm

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Hecke.Construction
