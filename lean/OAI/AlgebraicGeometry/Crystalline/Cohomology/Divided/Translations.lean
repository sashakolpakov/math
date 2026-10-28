import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineMaps

/-! # Translations -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Translations.DividedTranslations

noncomputable section

/-!
# Translation automorphisms of the actual relative divided-power algebra

Translating divided coordinates by elements of the coefficient PD ideal
is an algebra automorphism preserving the full relative divided powers.
Its inverse is translation by the negative coordinates. Coordinate
derivatives commute with both maps.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I)

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ

def map (b : σ → R) (hb : ∀ i, b i ∈ I) : G →ₐ[R] G :=
  AffineMaps.DividedAffineMaps.map R R σ I δ b hb

theorem map_coordinate (b : σ → R) (hb : ∀ i, b i ∈ I) (i : σ) :
    map R σ I δ b hb (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = algebraMap R G (b i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i :=
  AffineMaps.DividedAffineMaps.map_coordinate R R σ I δ b hb i

theorem map_isDPMorphism (b : σ → R) (hb : ∀ i, b i ∈ I) :
    DividedPowers.IsDPMorphism γ γ (map R σ I δ b hb).toRingHom :=
  AffineMaps.DividedAffineMaps.map_isDPMorphism R R σ I δ b hb I δ
    (DividedPowers.DPMorphism.id δ).isDPMorphism

theorem map_ext (f g : G →ₐ[R] G)
    (hf : DividedPowers.IsDPMorphism γ γ f.toRingHom)
    (hg : DividedPowers.IsDPMorphism γ γ g.toRingHom)
    (hX : ∀ i, f (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = g (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) : f = g := by
  have he := AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate R σ I δ G J γ
    f.toRingHom g.toRingHom hf hg (fun r => (f.commutes r).trans (g.commutes r).symm) hX
  exact AlgHom.ext (RingHom.congr_fun he)

theorem map_zero : map R σ I δ (fun _ => 0) (fun _ => (I).zero_mem) = AlgHom.id R G := by
  apply map_ext R σ I δ _ _ (map_isDPMorphism R σ I δ _ _) (DividedPowers.DPMorphism.id γ).isDPMorphism
  intro i
  rw [map_coordinate, _root_.map_zero, zero_add]
  rfl

theorem map_comp (b c : σ → R) (hb : ∀ i, b i ∈ I) (hc : ∀ i, c i ∈ I) :
    (map R σ I δ b hb).comp (map R σ I δ c hc) =
      map R σ I δ (fun i => b i + c i) (fun i => (I).add_mem (hb i) (hc i)) := by
  apply map_ext R σ I δ _ _
    ((map_isDPMorphism R σ I δ b hb).comp _ (map_isDPMorphism R σ I δ c hc))
    (map_isDPMorphism R σ I δ _ _)
  intro i
  change map R σ I δ b hb (map R σ I δ c hc (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i)) = _
  rw [map_coordinate, _root_.map_add, AlgHom.commutes, map_coordinate, map_coordinate, _root_.map_add]
  ac_rfl

theorem map_eq_id (b : σ → R) (hb : ∀ i, b i ∈ I) (hz : ∀ i, b i = 0) :
    map R σ I δ b hb = AlgHom.id R G := by
  apply map_ext R σ I δ _ _ (map_isDPMorphism R σ I δ _ _) (DividedPowers.DPMorphism.id γ).isDPMorphism
  intro i
  rw [map_coordinate, hz, _root_.map_zero, zero_add]
  rfl

def algebraEquiv (b : σ → R) (hb : ∀ i, b i ∈ I) : G ≃ₐ[R] G :=
  AlgEquiv.ofAlgHom (map R σ I δ b hb) (map R σ I δ (fun i => -b i) (fun i => (I).neg_mem (hb i)))
    (by
      rw [map_comp]
      exact map_eq_id R σ I δ _ _ (fun i => add_neg_cancel (b i)))
    (by
      rw [map_comp]
      exact map_eq_id R σ I δ _ _ (fun i => neg_add_cancel (b i)))

theorem algebraEquiv_isDPMorphism (b : σ → R) (hb : ∀ i, b i ∈ I) :
    DividedPowers.IsDPMorphism γ γ (algebraEquiv R σ I δ b hb).toRingHom :=
  map_isDPMorphism R σ I δ b hb

theorem algebraEquiv_symm_isDPMorphism (b : σ → R) (hb : ∀ i, b i ∈ I) :
    DividedPowers.IsDPMorphism γ γ (algebraEquiv R σ I δ b hb).symm.toRingHom :=
  map_isDPMorphism R σ I δ (fun i => -b i) (fun i => (I).neg_mem (hb i))

theorem derivative_equiv (b : σ → R) (hb : ∀ i, b i ∈ I) (i : σ) (t : G) :
    FreeDivided.Derivation.FreeDividedDerivation.derivation R σ i (algebraEquiv R σ I δ b hb t) =
      algebraEquiv R σ I δ b hb (FreeDivided.Derivation.FreeDividedDerivation.derivation R σ i t) :=
  AffineMaps.DividedAffineMaps.derivation_naturality R R σ I δ b hb i t

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Translations.DividedTranslations
