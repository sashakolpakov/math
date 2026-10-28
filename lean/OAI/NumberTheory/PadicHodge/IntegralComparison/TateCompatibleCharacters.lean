import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoefficientLimit

/-! # Tate Compatible Characters -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TateCompatibleCharacters

noncomputable section

/-! Compatible characters on the actual torsion groups pair with the
actual Tate inverse limit to give integral linear functionals. -/

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime] {H : Type u} [AddCommGroup H]

def compatible : AddSubgroup (∀ n, AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ H n →+ ZMod (ℓ ^ n)) where
  carrier := {χ | ∀ n t, χ n (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.transition ℓ n t) =
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n)) (χ (n + 1) t)}
  zero_mem' := by intro n t; exact (map_zero _).symm
  add_mem' := by
    intro x y hx hy n t
    change x n (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.transition ℓ n t) + y n (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.transition ℓ n t) = _
    rw [hx, hy]
    exact (map_add _ _ _).symm
  neg_mem' := by
    intro x hx n t
    change -x n (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.transition ℓ n t) = _
    rw [hx]
    exact (map_neg _ _).symm

omit [Fact (Nat.Prime ℓ)] in
theorem coherent_of_step (a : ∀ n, ZMod (ℓ ^ n))
    (ha : ∀ n, ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))
      (a (n + 1)) = a n) :
    ∀ m n (h : m ≤ n), ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (a n) = a m := by
  intro m n h
  induction n, h using Nat.le_induction with
  | base => exact congrArg (fun f : ZMod (ℓ ^ m) →+* ZMod (ℓ ^ m) => f (a m)) ZMod.castHom_self
  | succ n h ih =>
    have he := congrArg (fun f : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ m) => f (a (n + 1)))
      (ZMod.castHom_comp (pow_dvd_pow ℓ h) (pow_dvd_pow ℓ (Nat.le_succ n)))
    exact he.symm.trans ((congrArg (ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m))) (ha n)).trans ih)

def residues (χ : compatible (H := H) ℓ) (t : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ) :
    AlgebraicGeometry.FormalGeometry.Completion.CoefficientLimit.Construction.coherentFiniteCoefficients ℓ :=
  ⟨fun n => χ.val n (t.val n), coherent_of_step ℓ _ (fun n => by
    rw [← χ.property n, t.property n])⟩

def value (χ : compatible (H := H) ℓ) (t : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ) : ℤ_[ℓ] :=
  AlgebraicGeometry.FormalGeometry.Completion.CoefficientLimit.Construction.coherentFiniteLift ℓ (residues ℓ χ t)

@[simp] theorem value_reduction (χ : compatible (H := H) ℓ) (t : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ)
    (n : ℕ) : PadicInt.toZModPow n (value ℓ χ t) = χ.val n (t.val n) :=
  AlgebraicGeometry.FormalGeometry.Completion.CoefficientLimit.Construction.coherentFiniteLift_spec ℓ _ n

def toDual : compatible (H := H) ℓ →+ Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ) where
  toFun χ := {
    toFun := value ℓ χ
    map_add' t u := by
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      rw [map_add, value_reduction, value_reduction, value_reduction]
      exact (χ.val n).map_add _ _
    map_smul' a t := by
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      change PadicInt.toZModPow n (value ℓ χ (a • t)) =
        PadicInt.toZModPow n (a * value ℓ χ t)
      rw [map_mul, value_reduction, value_reduction]
      exact ZMod.map_smul (χ.val n) (PadicInt.toZModPow n a) (t.val n) }
  map_zero' := by
    apply LinearMap.ext
    intro t
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    exact (value_reduction ℓ 0 t n).trans (map_zero _).symm
  map_add' χ ψ := by
    apply LinearMap.ext
    intro t
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    change PadicInt.toZModPow n (value ℓ (χ + ψ) t) =
      PadicInt.toZModPow n (value ℓ χ t + value ℓ ψ t)
    rw [map_add, value_reduction, value_reduction, value_reduction]
    rfl

theorem toDual_injective (hdiv : ∀ x : H, ∃ y, ℓ • y = x) :
    Function.Injective (toDual (H := H) ℓ) := by
  intro χ ψ h
  apply Subtype.ext
  funext n
  apply AddMonoidHom.ext
  intro t
  obtain ⟨s, rfl⟩ := AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate_surjective ℓ hdiv n t
  have he := congrArg (fun f : Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ) =>
    PadicInt.toZModPow n (f s)) h
  exact (value_reduction ℓ χ s n).symm.trans (he.trans (value_reduction ℓ ψ s n))

variable (hdiv : ∀ x : H, ∃ y, ℓ • y = x)

def finiteCharacter (f : Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ)) (n : ℕ) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ H n →+ ZMod (ℓ ^ n) :=
  (QuotientAddGroup.lift (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate (H := H) ℓ n).toAddMonoidHom.ker
    ((PadicInt.toZModPow n).toAddMonoidHom.comp f.toAddMonoidHom) (by
      intro t ht
      obtain ⟨s, rfl⟩ := (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate_eq_zero_iff ℓ n t).mp ht
      change PadicInt.toZModPow n (f ((ℓ : ℤ_[ℓ]) ^ n • s)) = 0
      rw [map_smul, smul_eq_mul, map_mul, map_pow, map_natCast]
      have hz : (ℓ : ZMod (ℓ ^ n)) ^ n = 0 := by
        rw [← Nat.cast_pow, CharP.cast_eq_zero]
      rw [hz, zero_mul])).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate (H := H) ℓ n).toAddMonoidHom
      (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate_surjective ℓ hdiv n)).symm.toAddMonoidHom

theorem finiteCharacter_evaluate (f : Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ))
    (n : ℕ) (t : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ) :
    finiteCharacter ℓ hdiv f n (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate ℓ n t) = PadicInt.toZModPow n (f t) := by
  let e := QuotientAddGroup.quotientKerEquivOfSurjective
    (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate (H := H) ℓ n).toAddMonoidHom (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate_surjective ℓ hdiv n)
  have he : e (QuotientAddGroup.mk t) = AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate ℓ n t := rfl
  dsimp only [finiteCharacter, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe]
  rw [← he, e.symm_apply_apply]
  rfl

def fromDual (f : Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ)) : compatible (H := H) ℓ :=
  ⟨finiteCharacter ℓ hdiv f, by
    intro n t
    obtain ⟨s, rfl⟩ := AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate_surjective ℓ hdiv (n + 1) t
    have ht : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.transition ℓ n (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate ℓ (n + 1) s) = AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate ℓ n s := s.property n
    rw [ht, finiteCharacter_evaluate, finiteCharacter_evaluate]
    exact (congrArg (fun r : ℤ_[ℓ] →+* ZMod (ℓ ^ n) => r (f s))
      (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n))).symm⟩

theorem toDual_fromDual (f : Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ)) :
    toDual ℓ (fromDual ℓ hdiv f) = f := by
  apply LinearMap.ext
  intro t
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  exact (value_reduction ℓ (fromDual ℓ hdiv f) t n).trans
    (finiteCharacter_evaluate ℓ hdiv f n t)

def equiv : compatible (H := H) ℓ ≃+ Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := H) ℓ) :=
  AddEquiv.ofBijective (toDual ℓ)
    ⟨toDual_injective ℓ hdiv, fun f => ⟨fromDual ℓ hdiv f, toDual_fromDual ℓ hdiv f⟩⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TateCompatibleCharacters
