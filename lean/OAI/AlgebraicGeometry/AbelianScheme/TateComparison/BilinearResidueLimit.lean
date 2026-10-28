import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PadicResidueLimit

/-! # Bilinear Residue Limit -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearResidueLimit

noncomputable section

/-! Compatible finite-level bilinear residues construct an integral
p-adic bilinear form. Its values, additivity and scalar laws are all
detected by the actual residue maps. -/

variable (q : ℕ) [Fact q.Prime]
  {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module ℤ_[q] V] [Module ℤ_[q] W]
  (β : ∀ n : ℕ, V →+ W →+ ZMod (q ^ n))
  (hc : ∀ (m n : ℕ) (h : m ≤ n) (x : V) (y : W),
    ZMod.castHom (pow_dvd_pow q h) (ZMod (q ^ m)) (β n x y) = β m x y)

private def bilinearResidueValue (x : V) (y : W) : ℤ_[q] :=
  PadicResidueLimit.padicResidueLimit q ⟨fun n => β n x y, fun m n h => hc m n h x y⟩

omit [Module ℤ_[q] V] [Module ℤ_[q] W] in
private theorem bilinearResidueValue_spec (x : V) (y : W) (n : ℕ) :
    PadicInt.toZModPow n (bilinearResidueValue q β hc x y) = β n x y :=
  PadicResidueLimit.padicResidueLimit_spec q _ n

variable
  (hleft : ∀ (n : ℕ) (a : ℤ_[q]) (x : V) (y : W),
    β n (a • x) y = PadicInt.toZModPow n a * β n x y)
  (hright : ∀ (n : ℕ) (a : ℤ_[q]) (x : V) (y : W),
    β n x (a • y) = PadicInt.toZModPow n a * β n x y)

def bilinearResidueLimit : V →ₗ[ℤ_[q]] W →ₗ[ℤ_[q]] ℤ_[q] where
  toFun x := {
    toFun := bilinearResidueValue q β hc x
    map_add' y z := by
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      simp only [bilinearResidueValue_spec, map_add]
    map_smul' a y := by
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      change PadicInt.toZModPow n (bilinearResidueValue q β hc x (a • y)) =
        PadicInt.toZModPow n (a * bilinearResidueValue q β hc x y)
      rw [map_mul, bilinearResidueValue_spec, bilinearResidueValue_spec, hright] }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    change PadicInt.toZModPow n (bilinearResidueValue q β hc (x + z) y) =
      PadicInt.toZModPow n (bilinearResidueValue q β hc x y + bilinearResidueValue q β hc z y)
    simp only [bilinearResidueValue_spec, map_add, AddMonoidHom.add_apply]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    change PadicInt.toZModPow n (bilinearResidueValue q β hc (a • x) y) =
      PadicInt.toZModPow n (a * bilinearResidueValue q β hc x y)
    rw [map_mul, bilinearResidueValue_spec, bilinearResidueValue_spec, hleft]

theorem bilinearResidueLimit_spec (x : V) (y : W) (n : ℕ) :
    PadicInt.toZModPow n (bilinearResidueLimit q β hc hleft hright x y) = β n x y :=
  bilinearResidueValue_spec q β hc x y n

theorem bilinearResidueLimit_unique (B : V →ₗ[ℤ_[q]] W →ₗ[ℤ_[q]] ℤ_[q])
    (hB : ∀ (x : V) (y : W) (n : ℕ), PadicInt.toZModPow n (B x y) = β n x y) :
    B = bilinearResidueLimit q β hc hleft hright := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  exact (hB x y n).trans (bilinearResidueLimit_spec q β hc hleft hright x y n).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearResidueLimit
