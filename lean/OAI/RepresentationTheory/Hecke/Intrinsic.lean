import OAI.RepresentationTheory.Hecke.CentralConstraint
import OAI.RepresentationTheory.Hecke.Betti
import OAI.RepresentationTheory.Hecke.SphericalActionModelInverse
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TorusRestriction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Intrinsic -/

namespace OAI.RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic

noncomputable section

/-!
# Native CentralConstraint

The full Betti action is the tensor extension of TateComparison's actual rational
pullback. The active restriction is the canonical SL3-to-GL3-to-full-Hecke
embedding. Complete instantiated SphericalAction, CentralAction and Commuting conclusions are the
named conditional inputs. The native GL3 kernel calculations prove the
needed GL3/RationalStructure/CosetCalculus consequences, so their abstract specifications are not
additional hypotheses: normalized minuscule integrals, the central kernel,
rational coefficient extension, and projective restriction are all proved
on the same canonical operators. Finiteness uses the proved projective
Betti finiteness theorem underlying Kunneth.

TateComparison's raw kernels use inverse representatives. Thus a normalized torus
parameter β from SphericalAction gives raw minuscule coordinates β⁻¹. The verified
inversion helper swaps the first two entries, so the parameter here is
`(parameterForConvention c e₀)⁻¹`. No norm-to-algebraicity inference occurs.
-/

open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TorusRestriction

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def nativeActiveInclusion : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
    (Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.reference.distinguished
      (Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.reference.distinguished))

def nativeActiveCharacter (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ) :
    SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ := χ.comp (nativeActiveInclusion D)

def nativeActiveAction (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) :
    SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D) :=
  (Betti.CentralConstraintIntrinsic.nativeFullAction D A).comp (nativeActiveInclusion D)

theorem native_full_parameters_algebraic
    (hg : D.HasIntegralModelGeometry) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥) :
    ∀ i, IsAlgebraic ℚ (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D ℂ (Betti.CentralConstraintIntrinsic.actionProjection D A) χ i) := by
  have hevals := Betti.CentralConstraintIntrinsic.native_rational_eigenvalues_algebraic D hg A χ hχ
  obtain ⟨_, h₁, h₂, h₃⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple_spec D ℂ (Betti.CentralConstraintIntrinsic.actionProjection D A) χ
  exact Rational.CentralConstraintIntrinsic.cubic_parameters_algebraic q (Fact.out : q.Prime).ne_zero
    (χ (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (Betti.CentralConstraintIntrinsic.actionProjection D A) 1))
    (χ (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (Betti.CentralConstraintIntrinsic.actionProjection D A) 2))
    (χ (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished))
    (hevals _) (hevals _) (hevals _)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D ℂ (Betti.CentralConstraintIntrinsic.actionProjection D A) χ) h₁ h₂ h₃

theorem native_projective_parameters_from_SphericalAction
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (c : SphericalActionModelInverse.ActingConvention)
    (Θ : SphericalActionModelInverse.Radial q →ₗ[ℂ] ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D)
    (M : ℕ) (ω : ℂ)
    (hSphericalAction : SphericalActionModelInverse.RadialSatakeConclusion q c
      (nativeActiveAction D A) Θ M ω)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hΘχ : ∃ v : ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D, v ∈ LinearMap.range Θ ∧ v ≠ 0 ∧
      ∀ h, nativeActiveAction D A h v = nativeActiveCharacter D χ h • v) :
    ∃ e₀ : ℂ, e₀ ≠ 0 ∧ e₀ ^ M = ω ∧
      ∃ a : ℂ, a ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
        ∀ i, AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D ℂ (Betti.CentralConstraintIntrinsic.actionProjection D A) χ i = a *
          (![(Real.sqrt (q : ℝ) : ℂ), (Real.sqrt (q : ℝ) : ℂ)⁻¹,
            (SphericalActionModelInverse.parameterForConvention c e₀)⁻¹] : Fin 3 → ℂ) (σ i) := by
  obtain ⟨e₀, he₀, hroot, _, β, hβ, hβproj⟩ :=
    hSphericalAction.2.2 (nativeActiveCharacter D χ) hΘχ
  have hrestriction (S : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
      χ (1 ⊗ₜ[ℚ] Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.reference.distinguished
        (Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.reference.distinguished) S) =
          AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β S := by
    have h := DFunLike.congr_fun hβ (1 ⊗ₜ[ℚ] S)
    rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver_complex]
    exact h
  obtain ⟨a, ha, σ, hαβ⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TorusRestriction.native_full_projective_torus_restriction D ℂ
    (Betti.CentralConstraintIntrinsic.actionProjection D A) hg hq hIsogenyQuotient (Betti.CentralConstraintIntrinsic.actionProjection_realizes D hg hq hIsogenyQuotient A hTateComparison)
    (AlgHom.id ℚ ℂ) β χ hrestriction
  obtain ⟨b, hb, τ, hβinv⟩ := CentralConstraint.Construction.projective_parameter_under_inversion
    (Real.sqrt (q : ℝ) : ℂ) (SphericalActionModelInverse.parameterForConvention c e₀)
    (fun i => (β i : ℂ)) hβproj
  refine ⟨e₀, he₀, hroot, a * b, mul_ne_zero ha hb, σ.trans τ, ?_⟩
  intro i
  rw [hαβ, hβinv]
  simp only [Equiv.trans_apply, mul_assoc]

/-- The manuscript constraint for every occurring full character whose
actual active restriction occurs in the indicated theta image. -/
theorem native_central_constraint_on_full_satake_extensions
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (fullSide : Fin s → Bool)
    (hCentralAction : Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished fullSide)
    (c : SphericalActionModelInverse.ActingConvention)
    (Θ : SphericalActionModelInverse.Radial q →ₗ[ℂ] ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D)
    (M : ℕ) (ω : ℂ)
    (hSphericalAction : SphericalActionModelInverse.RadialSatakeConclusion q c
      (nativeActiveAction D A) Θ M ω)
    (hCommuting : letI := Betti.CentralConstraintIntrinsic.rationalBetti_finite D hg
      CentralConstraint.Construction.CommutingInput (fun h => Betti.CentralConstraintIntrinsic.nativeFullAction D A h))
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hΘχ : ∃ v : ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D, v ∈ LinearMap.range Θ ∧ v ≠ 0 ∧
      ∀ h, nativeActiveAction D A h v = nativeActiveCharacter D χ h • v) :
    let α := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D ℂ (Betti.CentralConstraintIntrinsic.actionProjection D A) χ
    let C := (1 : ℂ) ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide
    let r := (Real.sqrt (q : ℝ) : ℂ)
    ∃ e₀ : ℂ, e₀ ≠ 0 ∧ e₀ ^ M = ω ∧
      let e := (SphericalActionModelInverse.parameterForConvention c e₀)⁻¹
      IsAlgebraic ℚ e ∧
      ∃ b : ℂ, ∃ σ : Equiv.Perm (Fin 3),
        b ≠ 0 ∧ IsAlgebraic ℚ b ∧ (∀ i, IsAlgebraic ℚ (α i)) ∧
        (∀ i, χ C * α i = b * (![r, r⁻¹, e] : Fin 3 → ℂ) (σ i)) ∧
        b ^ 3 * e = (χ C) ^ 3 * χ (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished) ∧
        (∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1 ∧
          ∀ γ : ℂ ≃ₐ[ℚ] ℂ, ((γ b) ^ 3 * γ e) ^ n = 1) ∧
        χ (C * (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (Betti.CentralConstraintIntrinsic.actionProjection D A) 1)) =
          (q : ℂ) * b * (r + r⁻¹ + e) ∧
        χ (C ^ 2 * (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (Betti.CentralConstraintIntrinsic.actionProjection D A) 2)) =
          (q : ℂ) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e) := by
  let := Betti.CentralConstraintIntrinsic.rationalBetti_finite D hg
  let : CommRing (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
    { (inferInstance : Ring (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with
      mul_comm := AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q (SphericalActionModelInverse.cartanInput q) }
  obtain ⟨e₀, he₀, hroot, hproj⟩ := native_projective_parameters_from_SphericalAction
    D hg hq hIsogenyQuotient A hTateComparison c Θ M ω hSphericalAction χ hΘχ
  let r : ℂ := (Real.sqrt (q : ℝ) : ℂ)
  let e : ℂ := (SphericalActionModelInverse.parameterForConvention c e₀)⁻¹
  have hr : r ^ 2 = (q : ℂ) := by
    dsimp [r]
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hrne : r ≠ 0 := by
    intro hz
    have hzero : (q : ℂ) = 0 := by simpa only [hz, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] using hr.symm
    exact (Fact.out : q.Prime).ne_zero (Nat.cast_eq_zero.mp hzero)
  have hralg : IsAlgebraic ℚ r :=
    IsAlgebraic.of_pow (n := 2) (by decide) (hr.symm ▸ isAlgebraic_natCast q)
  have he : e ≠ 0 := by
    cases c <;> simp [e, SphericalActionModelInverse.parameterForConvention, he₀]
  have healg : IsAlgebraic ℚ e := Rational.CentralConstraintIntrinsic.projective_parameter_algebraic r e hrne hralg
    _ (native_full_parameters_algebraic D hg A χ hχ) hproj
  refine ⟨e₀, he₀, hroot, healg, ?_⟩
  obtain ⟨_, h₁, h₂, h₃⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple_spec D ℂ (Betti.CentralConstraintIntrinsic.actionProjection D A) χ
  exact CentralConstraint.Construction.central_constraint_on_full_satake_extensions
    (K := ℂ) (H := ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (V := ℂ ⊗[ℚ] Betti.CentralConstraintIntrinsic.RationalBetti D)
    (Betti.CentralConstraintIntrinsic.nativeFullAction D A) χ hCommuting q (Fact.out : q.Prime) r e hr he healg
    (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (Betti.CentralConstraintIntrinsic.actionProjection D A) 1)
    (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (Betti.CentralConstraintIntrinsic.actionProjection D A) 2)
    (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished)
    (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D ℂ (Betti.CentralConstraintIntrinsic.actionProjection D A) χ) hχ
    (Betti.CentralConstraintIntrinsic.native_central_scalar_extension D A D.reference.distinguished fullSide hCentralAction)
    h₁ h₂ h₃ hproj

end

end OAI.RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic
