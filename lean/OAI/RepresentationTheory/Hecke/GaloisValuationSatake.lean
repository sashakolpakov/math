import OAI.RepresentationTheory.Hecke.IntrinsicParameters

/-! # Galois Valuation Satake -/

namespace OAI.RepresentationTheory.Hecke.GaloisValuationSatake

noncomputable section

/-! The native SL3 coefficient formula is a finite rational kernel sum times
q to an integral power. Its already proved base-change identity discharges
the actual Satake transport directly, without a general RationalStructure input. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.SphericalActionModelInverse

open OAI.RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic

lemma lift_actual_satake (q : ℕ) [Fact q.Prime]
    (j : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar →+* ℂ) (s e : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar) (hs : s ≠ 0) (he : e ≠ 0)
    (χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ) (α : Fin 3 → ℂˣ)
    (hχα : SphericalActionModelInverse.HasSatakeParameter q χ α)
    (hα : SphericalActionModelInverse.ProjectivelyEqual (fun i => (α i : ℂ))
      (fun i => j (GaloisValuationCm.parameterTriple s e i))) :
    ∃ β : Fin 3 → IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ,
      GaloisValuationCm.ProjectivelyEqual (fun i => (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)) (GaloisValuationCm.parameterTriple s e) ∧
      (∀ T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        j (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = χ (1 ⊗ₜ[ℚ] T)) ∧
      ∀ (σ : Gal(IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ)) (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q),
        σ (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) =
          AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map σ.toMonoidHom (β i)) T := by
  obtain ⟨β, hβ, z, hz⟩ := IntrinsicParameters.GaloisValuationIntrinsic.lift_projective_triple j s e hs he α hα
  refine ⟨β, hβ, ?_, ?_⟩
  · intro T
    change j.toRatAlgHom (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = _
    rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver_map q j.toRatAlgHom]
    have hh : χ (1 ⊗ₜ[ℚ] T) = AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q α T := by
      rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver_complex]
      exact DFunLike.congr_fun hχα _
    rw [hh, hz, AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver_scale]
    rfl
  · intro σ T
    exact AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver_map q σ.toAlgHom β T

end

end OAI.RepresentationTheory.Hecke.GaloisValuationSatake
