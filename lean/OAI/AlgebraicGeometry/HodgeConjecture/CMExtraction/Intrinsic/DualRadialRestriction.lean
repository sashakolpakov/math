import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TorusRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadialSatake

/-! # Dual Radial Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.DualRadialRestriction

noncomputable section

/-! The inverse-transpose radial character forces the dilation root in the
actual normalized native full triple, with the same chosen complex closure. -/

open scoped Classical TensorProduct _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadialSatake.Iwasawa

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem native_full_dual_radial_projective (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (hA : A.IsRealization D hg hq hIsogenyQuotient)
    (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbarˣ) (χ : ParameterChoices.Qbar ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ParameterChoices.Qbar] ParameterChoices.Qbar)
    (he : ∀ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      j (χ (1 ⊗ₜ[ℚ] RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.reference.distinguished
        (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.reference.distinguished) S)) =
          DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.map j.toMonoidHom a) (1 ⊗ₜ[ℚ] S)) :
    ∃ c : ParameterChoices.Qbar, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, MinusculeParameters.nativeFullParameterTriple D ParameterChoices.Qbar A χ i = c *
        (![DualRadialSatake.Iwasawa.algebraicSqrt q j, (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹, (a : ParameterChoices.Qbar)] : Fin 3 → ParameterChoices.Qbar) (σ i) := by
  have ht : ∀ S : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      χ (1 ⊗ₜ[ℚ] RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.reference.distinguished
        (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.reference.distinguished) S) =
          SatakeBaseChange.Iwasawa.torusSatakeOver q (DualRadialSatake.Iwasawa.algebraicDualRadialTorusPoint q j a) S := by
    intro S
    apply j.injective
    exact (he S).trans (DualRadialSatake.Iwasawa.algebraicDualRadialSatakeCharacter_image q j a S).symm
  obtain ⟨c, hc, σ, hσ⟩ := TorusRestriction.native_full_projective_torus_restriction D ParameterChoices.Qbar A hg hq hIsogenyQuotient hA
    j.toRatAlgHom (DualRadialSatake.Iwasawa.algebraicDualRadialTorusPoint q j a) χ ht
  refine ⟨c, hc, σ.trans (Equiv.swap 0 1), ?_⟩
  intro i
  rw [hσ i]
  congr 1
  change (DualRadialSatake.Iwasawa.algebraicDualRadialTorusPoint q j a (σ i) : ParameterChoices.Qbar)⁻¹ =
    (![DualRadialSatake.Iwasawa.algebraicSqrt q j, (DualRadialSatake.Iwasawa.algebraicSqrt q j)⁻¹, (a : ParameterChoices.Qbar)] : Fin 3 → ParameterChoices.Qbar)
      (Equiv.swap 0 1 (σ i))
  generalize σ i = k
  fin_cases k <;> simp [DualRadialSatake.Iwasawa.algebraicDualRadialTorusPoint, DualRadialSatake.Iwasawa.algebraicSqrtUnit,
    Equiv.swap_apply_def, Fin.ext_iff]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.DualRadialRestriction
