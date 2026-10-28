import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineMaps

/-! # Power Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerNaturality.FreeRelativePowerNaturality

noncomputable section

/-! # Power-coordinate maps commute with changes of actual frame lifts -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R S σ : Type u) [CommRing R] [CommRing S]
  (I : Ideal R) (δ : DividedPowers I) (J : Ideal S) (ε : DividedPowers J)
  (m : ℕ) (a c : σ → R) (b d : σ → S)
  (hR : ∀ i, a i ^ m - c i ∈ I) (hS : ∀ i, b i ^ m - d i ∈ J)
  (φ : R →+* S)
  (f g : DividedPowerAlgebra R (σ →₀ R) →+* DividedPowerAlgebra S (σ →₀ S))
  (hf : DividedPowers.IsDPMorphism (Powers.FreeRelativePowers.dividedPowers R σ I δ)
    (Powers.FreeRelativePowers.dividedPowers S σ J ε) f)
  (hg : DividedPowers.IsDPMorphism (Powers.FreeRelativePowers.dividedPowers R σ I δ)
    (Powers.FreeRelativePowers.dividedPowers S σ J ε) g)
  (fc : ∀ r, f (algebraMap R (DividedPowerAlgebra R (σ →₀ R)) r) =
    algebraMap S (DividedPowerAlgebra S (σ →₀ S)) (φ r))
  (gc : ∀ r, g (algebraMap R (DividedPowerAlgebra R (σ →₀ R)) r) =
    algebraMap S (DividedPowerAlgebra S (σ →₀ S)) (φ r))
  (fX : ∀ i, f (PowerMap.FreeRelativePowerMap.total R σ a i) = PowerMap.FreeRelativePowerMap.total S σ b i)
  (gX : ∀ i, g (PowerMap.FreeRelativePowerMap.total R σ c i) = PowerMap.FreeRelativePowerMap.total S σ d i)

include hf hg fc gc fX gX in
theorem square :
    f.comp (PowerMap.FreeRelativePowerMap.map R σ I δ m a c hR).toRingHom =
      (PowerMap.FreeRelativePowerMap.map S σ J ε m b d hS).toRingHom.comp g := by
  let l := f.comp (PowerMap.FreeRelativePowerMap.map R σ I δ m a c hR).toRingHom
  let r := (PowerMap.FreeRelativePowerMap.map S σ J ε m b d hS).toRingHom.comp g
  have hc (x : R) : l (algebraMap R (DividedPowerAlgebra R (σ →₀ R)) x) =
      r (algebraMap R (DividedPowerAlgebra R (σ →₀ R)) x) := by
    change f (PowerMap.FreeRelativePowerMap.map R σ I δ m a c hR (algebraMap R _ x)) =
      PowerMap.FreeRelativePowerMap.map S σ J ε m b d hS (g (algebraMap R _ x))
    rw [AlgHom.commutes, fc, gc, AlgHom.commutes]
  have ht (i : σ) : l (PowerMap.FreeRelativePowerMap.total R σ c i) = r (PowerMap.FreeRelativePowerMap.total R σ c i) := by
    change f (PowerMap.FreeRelativePowerMap.map R σ I δ m a c hR (PowerMap.FreeRelativePowerMap.total R σ c i)) =
      PowerMap.FreeRelativePowerMap.map S σ J ε m b d hS (g (PowerMap.FreeRelativePowerMap.total R σ c i))
    rw [PowerMap.FreeRelativePowerMap.map_total, map_pow, fX, gX, PowerMap.FreeRelativePowerMap.map_total]
  apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate R σ I δ
    (DividedPowerAlgebra S (σ →₀ S)) (Multivariable.DividedPowers.MultivariableDividedPowers.ideal S σ J)
    (Powers.FreeRelativePowers.dividedPowers S σ J ε) l r
    (hf.comp _ (PowerMap.FreeRelativePowerMap.map_isDPMorphism R σ I δ m a c hR))
    ((PowerMap.FreeRelativePowerMap.map_isDPMorphism S σ J ε m b d hS).comp _ hg) hc
  intro i
  have he : Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i = PowerMap.FreeRelativePowerMap.total R σ c i -
      algebraMap R (DividedPowerAlgebra R (σ →₀ R)) (c i) := by
    dsimp only [PowerMap.FreeRelativePowerMap.total]
    abel
  rw [he, map_sub, map_sub, ht, hc]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerNaturality.FreeRelativePowerNaturality
