import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialTransfer
import OAI.AlgebraicGeometry.Crystalline.Cohomology.AdditiveNatural
import Mathlib.Algebra.Homology.QuasiIso

/-! # Polynomial Transfer Inversion -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialTransferInversion.PrimePolynomialTransferInversion

noncomputable section

/-!
# Inverting the bounded integral polynomial Frobenius transfer

Every additive functor to characteristic-zero vector spaces carries
the explicit transfer identities to a homotopy inverse. In particular,
this applies when integral p-adic completion precedes rationalization.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p]
  [Fintype σ] [LinearOrder σ]
  (L : Type u) [Field L] [CharZero L]
  (G : ModuleCat.{u} (WittVector p k) ⥤ ModuleCat.{u} L) [G.Additive]

local notation "W" => WittVector p k
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex W σ

abbrev complex : CochainComplex (ModuleCat.{u} L) ℕ := (G.mapHomologicalComplex (.up ℕ)).obj K

def frobenius : complex p k σ L G ⟶ complex p k σ L G :=
  (G.mapHomologicalComplex (.up ℕ)).map (PolynomialFrobeniusMap.PrimePolynomialFrobeniusMap.map p k σ)

def transfer : complex p k σ L G ⟶ complex p k σ L G :=
  (G.mapHomologicalComplex (.up ℕ)).map (PolynomialTransfer.PrimePolynomialTransfer.chain p k σ)

omit [CharZero L] in
theorem frobenius_transfer : frobenius p k σ L G ≫ transfer p k σ L G =
    (p : L) ^ Fintype.card σ • 𝟙 (complex p k σ L G) := by
  rw [frobenius, transfer, ← Functor.map_comp, PolynomialTransfer.PrimePolynomialTransfer.frobenius_chain,
    AdditiveNatural.AdditiveNaturalScalars.map_nat_pow_smul W L, CategoryTheory.Functor.map_id]

def transfer_homotopy : Homotopy
    ((p : L) ^ Fintype.card σ • 𝟙 (complex p k σ L G))
    (transfer p k σ L G ≫ frobenius p k σ L G) := by
  have h := G.mapHomotopy (PolynomialTransfer.PrimePolynomialTransfer.homotopy p k σ)
  simpa only [AdditiveNatural.AdditiveNaturalScalars.map_nat_pow_smul W L, CategoryTheory.Functor.map_id,
    Functor.map_comp, transfer, frobenius] using h

def inverse : complex p k σ L G ⟶ complex p k σ L G :=
  ((p : L) ^ Fintype.card σ)⁻¹ • transfer p k σ L G

theorem frobenius_inverse : frobenius p k σ L G ≫ inverse p k σ L G =
    𝟙 (complex p k σ L G) := by
  rw [inverse, Linear.comp_smul, frobenius_transfer, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime)))),
    one_smul]

def inverse_homotopy : Homotopy (inverse p k σ L G ≫ frobenius p k σ L G)
    (𝟙 (complex p k σ L G)) := by
  have hp : (p : L) ^ Fintype.card σ ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime)))
  have h := (transfer_homotopy p k σ L G).symm.smul (((p : L) ^ Fintype.card σ)⁻¹)
  simpa only [inverse, Linear.smul_comp, smul_smul,
    inv_mul_cancel₀ hp, one_smul] using h

def homotopyEquiv : HomotopyEquiv (complex p k σ L G) (complex p k σ L G) where
  hom := frobenius p k σ L G
  inv := inverse p k σ L G
  homotopyHomInvId := by rw [frobenius_inverse]
  homotopyInvHomId := inverse_homotopy p k σ L G

instance frobenius_quasiIso : QuasiIso (frobenius p k σ L G) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv p k σ L G)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialTransferInversion.PrimePolynomialTransferInversion
