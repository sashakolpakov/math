import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface

/-! # Localized Conormal Bases -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBases

noncomputable section

/-! Localizing an ideal transports its actual conormal and quotient
differential bases. The formulas preserve the classes of the original
defining equations and the universal Kähler differential maps. -/

open scoped TensorProduct

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (r : A) [IsLocalization.Away r B] (I : Ideal A)

abbrev extendedIdeal : Ideal B := I.map (algebraMap A B)

local instance quotientLocalization :
    IsLocalization.Away (Ideal.Quotient.mk I r) (B ⧸ extendedIdeal (B := B) I) :=
  AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction.quotient_extended_ideal_isLocalizationAway r I

local instance cotangentModule : Module (A ⧸ I) (extendedIdeal (B := B) I).Cotangent :=
  AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction.extendedCotangentQuotientModule I

local instance cotangentTower :
    IsScalarTower (A ⧸ I) (B ⧸ extendedIdeal (B := B) I) (extendedIdeal (B := B) I).Cotangent :=
  AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap_scalarTower I

def conormalEquiv :
    (B ⧸ extendedIdeal (B := B) I) ⊗[A ⧸ I] I.Cotangent ≃ₗ[B ⧸ extendedIdeal (B := B) I]
      (extendedIdeal (B := B) I).Cotangent := by
  have h := AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap_isLocalizedModule (S := B) r I
  exact ((isLocalizedModule_iff_isBaseChange (Submonoid.powers (Ideal.Quotient.mk I r))
    (B ⧸ extendedIdeal (B := B) I) (AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap (S := B) I)).mp h).equiv

theorem conormalEquiv_tmul (a : B ⧸ extendedIdeal (B := B) I) (x : I.Cotangent) :
    conormalEquiv (B := B) r I (a ⊗ₜ[A ⧸ I] x) =
      a • AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap (S := B) I x := rfl

def conormalBasis {c : ℕ} (b : Module.Basis (Fin c) (A ⧸ I) I.Cotangent) :
    Module.Basis (Fin c) (B ⧸ extendedIdeal (B := B) I) (extendedIdeal (B := B) I).Cotangent :=
  (b.baseChange (B ⧸ extendedIdeal (B := B) I)).map (conormalEquiv r I)

theorem conormalBasis_apply {c : ℕ} (b : Module.Basis (Fin c) (A ⧸ I) I.Cotangent) (i : Fin c) :
    conormalBasis (B := B) r I b i = AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction.extendedQuotientCotangentMap (S := B) I (b i) := by
  rw [conormalBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    conormalEquiv_tmul, one_smul]

theorem conormalBasis_equations {c : ℕ} (b : Module.Basis (Fin c) (A ⧸ I) I.Cotangent)
    (s : Fin c → I) (hb : ∀ i, b i = I.toCotangent (s i)) (i : Fin c) :
    conormalBasis (B := B) r I b i = (extendedIdeal (B := B) I).toCotangent
      ⟨algebraMap A B (s i).val, Ideal.mem_map_of_mem _ (s i).property⟩ := by
  rw [conormalBasis_apply, hb]
  rfl

include r in
theorem quotientFormallyEtale :
    Algebra.FormallyEtale (A ⧸ I) (B ⧸ extendedIdeal (B := B) I) :=
  Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (Ideal.Quotient.mk I r))

local instance quotientBaseTower : IsScalarTower k (A ⧸ I) (B ⧸ extendedIdeal (B := B) I) :=
  AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I

def quotientEquiv :
    (B ⧸ extendedIdeal (B := B) I) ⊗[A ⧸ I] Ω[A ⧸ I⁄k] ≃ₗ[B ⧸ extendedIdeal (B := B) I]
      Ω[B ⧸ extendedIdeal (B := B) I⁄k] := by
  letI := quotientFormallyEtale (B := B) r I
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (A ⧸ I) (B ⧸ extendedIdeal (B := B) I)

def quotientBasis {g : ℕ} (b : Module.Basis (Fin g) (A ⧸ I) Ω[A ⧸ I⁄k]) :
    Module.Basis (Fin g) (B ⧸ extendedIdeal (B := B) I) Ω[B ⧸ extendedIdeal (B := B) I⁄k] :=
  (b.baseChange (B ⧸ extendedIdeal (B := B) I)).map (quotientEquiv r I)

theorem quotientBasis_apply {g : ℕ} (b : Module.Basis (Fin g) (A ⧸ I) Ω[A ⧸ I⁄k]) (i : Fin g) :
    quotientBasis (B := B) r I b i = KaehlerDifferential.map k k (A ⧸ I)
      (B ⧸ extendedIdeal (B := B) I) (b i) := by
  rw [quotientBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply]
  exact (KaehlerDifferential.mapBaseChange_tmul k (A ⧸ I)
    (B ⧸ extendedIdeal (B := B) I) 1 (b i)).trans (one_smul _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalBases
