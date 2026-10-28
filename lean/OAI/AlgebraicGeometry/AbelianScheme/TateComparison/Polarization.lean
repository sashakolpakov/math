import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PrimeToIsogeny

/-! # Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Polarization

noncomputable section

/-! The supplied geometric polarization type makes its kernel prime to
the good prime. Its actual map on integral Tate modules is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u
variable {S : Scheme.{u}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  {k : Type u} [Field k] [IsAlgClosed k] (b : Spec (.of k) ⟶ S)

theorem polarization_kernelCard (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (δ : Fin g → ℕ)
    (hδ : f.HasPolarizationType δ) :
    Nat.card (f.kernelAt (Over.mk b)) = (∏ i, δ i) ^ 2 := by
  obtain ⟨e⟩ := hδ.geometricKernel k b
  rw [Nat.card_congr e.toEquiv]
  change Nat.card ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i))) = _
  simp [Nat.card_prod, Nat.card_pi, Nat.card_zmod, pow_two]

def polarizationTateEquiv (q : ℕ) [Fact q.Prime] (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
    (δ : Fin g → ℕ) (hδ : f.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i)) :
    Add.schemeTateModule A.scheme (Over.mk b) q ≃ₗ[ℤ_[q]]
      Add.schemeTateModule B.scheme (Over.mk b) q :=
  PrimeToIsogeny.geometricIntegralTateIsogenyEquiv b q f (by
    rw [polarization_kernelCard b f δ hδ, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hq.pow_right 2)

theorem polarizationTateEquiv_toLinearMap (q : ℕ) [Fact q.Prime]
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (δ : Fin g → ℕ)
    (hδ : f.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i)) :
    (polarizationTateEquiv b q f δ hδ hq).toLinearMap =
      Add.schemeTateMap A.scheme (Over.mk b) q f.hom := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Polarization
