import OAI.NumberTheory.PadicHodge.IntrinsicParameters
import OAI.RepresentationTheory.Hecke.GeometricParameters
import OAI.RepresentationTheory.Hecke.ThetaCentral
import OAI.LinearAlgebra.Endomorphisms.Commuting

/-! # Theta Parameters -/

namespace OAI.NumberTheory.PadicHodge.ThetaParameters.FrobeniusSlope

noncomputable section

/-! Apply CentralConstraint to the retained GaloisValuation torus triple and its specified root.
The radial root is not selected a second time. -/

open scoped TensorProduct
open OAI.RepresentationTheory.Hecke.ThetaCentral.ConstraintIntrinsic

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem raw_projective_from_retained_triple
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (j : AlgebraicClosure ℚ →+* ℂ) (r a : AlgebraicClosure ℚ)
    (hr : j r = (Real.sqrt (q : ℝ) : ℂ))
    (β : Fin 3 → (AlgebraicClosure ℚ)ˣ)
    (hβ : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (fun i => (β i : AlgebraicClosure ℚ))
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple r a⁻¹))
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχβ : ∀ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      j (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ (1 ⊗ₜ[ℚ] T)) :
    ∃ z : ℂ, z ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D ℂ (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) χ i =
        z * (![(Real.sqrt (q : ℝ) : ℂ), (Real.sqrt (q : ℝ) : ℂ)⁻¹, j a] : Fin 3 → ℂ) (σ i) := by
  let βc := fun i => Units.map j.toMonoidHom (β i)
  have hrestriction (T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
      χ (1 ⊗ₜ[ℚ] RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.reference.distinguished
        (RepresentationTheory.Theta.Geometric.Active.Algebra.Spherical.activeHeckeEquiv q D.reference.distinguished) T) = AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q βc T := by
    exact (hχβ T).symm.trans (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver_map q j.toRatAlgHom β T)
  obtain ⟨z, hz, σ, hfull⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TorusRestriction.native_full_projective_torus_restriction D ℂ
    (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) hg hq hIsogenyQuotient (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection_realizes D hg hq hIsogenyQuotient A hA)
    (AlgHom.id ℚ ℂ) βc χ hrestriction
  have hβc : RepresentationTheory.Hecke.SphericalActionModelInverse.ProjectivelyEqual
      (fun i => (βc i : ℂ))
      (![(Real.sqrt (q : ℝ) : ℂ), (Real.sqrt (q : ℝ) : ℂ)⁻¹, (j a)⁻¹] : Fin 3 → ℂ) := by
    obtain ⟨d, hd, τ, hτ⟩ := hβ
    refine ⟨j d, (map_ne_zero j).mpr hd, τ, ?_⟩
    intro i
    have h := congrArg j (hτ i)
    rw [map_mul] at h
    change j (β i : AlgebraicClosure ℚ) = _
    rw [h]
    congr 1
    generalize τ i = k
    fin_cases k <;> simp [RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple, hr]
  obtain ⟨w, hw, τ, hinv⟩ := RepresentationTheory.Hecke.CentralConstraint.Construction.projective_parameter_under_inversion
    (Real.sqrt (q : ℝ) : ℂ) (j a)⁻¹ (fun i => (βc i : ℂ)) hβc
  refine ⟨z * w, mul_ne_zero hz hw, σ.trans τ, ?_⟩
  intro i
  rw [hfull, hinv]
  simp only [inv_inv, Equiv.trans_apply, mul_assoc]

theorem central_values_from_retained_root
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (side : Fin s → Bool) (hCentralAction : RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished side)
    (j : AlgebraicClosure ℚ →+* ℂ) (r a : AlgebraicClosure ℚ)
    (hr : j r = (Real.sqrt (q : ℝ) : ℂ)) (ha : a ≠ 0)
    (β : Fin 3 → (AlgebraicClosure ℚ)ˣ)
    (hβ : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (fun i => (β i : AlgebraicClosure ℚ))
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple r a⁻¹))
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hχβ : ∀ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      j (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ (1 ⊗ₜ[ℚ] T)) :
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      ∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j χ hχ
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side i) =
          IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i := by
  let := RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.rationalBetti_finite D hg
  let : CommRing (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
    { (inferInstance : Ring (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with
      mul_comm := AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q (RepresentationTheory.Hecke.SphericalActionModelInverse.cartanInput q) }
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have healg : IsAlgebraic ℚ (j a) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).algHom j.toRatAlgHom
  have hproj := raw_projective_from_retained_triple D hg hq hIsogenyQuotient A hA j r a hr β hβ χ hχβ
  have h67 : RepresentationTheory.Hecke.CentralConstraint.Construction.CommutingInput (fun h => RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h) := by
    intro hc
    exact LinearAlgebra.Endomorphisms.Commuting.Construction.commuting_family_structure _ hc
  obtain ⟨_, h₁, h₂, h₃⟩ := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple_spec D ℂ (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) χ
  obtain ⟨bc, _σ, hbc, hbalg, _halg, _hproj, hcentral, ⟨n, hn, hpow, _hconj⟩, h₁c, h₂c⟩ :=
    RepresentationTheory.Hecke.CentralConstraint.Construction.central_constraint_on_full_satake_extensions
      (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A) χ h67 q (Fact.out : q.Prime)
      (Real.sqrt (q : ℝ) : ℂ) (j a) (IntrinsicParameters.FrobeniusSlopeIntrinsic.complexSqrt_sq q)
      ((map_ne_zero j).mpr ha) healg
      (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1)
      (1 ⊗ₜ[ℚ] AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 2)
      (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished)
      (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished side)
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D ℂ (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) χ) hχ
      (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.native_central_scalar_extension D A D.reference.distinguished side hCentralAction) h₁ h₂ h₃ hproj
  let b := IntrinsicParameters.FrobeniusSlopeIntrinsic.liftComplexAlgebraic j bc hbalg
  have hb : j b = bc := IntrinsicParameters.FrobeniusSlopeIntrinsic.liftComplexAlgebraic_image j bc hbalg
  refine ⟨b, (fun hz => hbc (by simpa only [hz, map_zero] using hb.symm)),
    ⟨n, hn, j.injective ?_⟩, ?_⟩
  · simpa only [map_pow, map_mul, map_one, hb] using hpow
  · intro i
    apply j.injective
    rw [IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter_image,
      IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues_map, hr, hb]
    let χrat := (χ.restrictScalars ℚ).comp Algebra.TensorProduct.includeRight
    have hmul (h k : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) : χ (1 ⊗ₜ[ℚ] (h * k)) =
        χ (1 ⊗ₜ[ℚ] h) * χ (1 ⊗ₜ[ℚ] k) := map_mul χrat h k
    have hpowrat (h : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (m : ℕ) : χ (1 ⊗ₜ[ℚ] (h ^ m)) =
        χ (1 ⊗ₜ[ℚ] h) ^ m := map_pow χrat h m
    fin_cases i
    · simpa [IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke, IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues,
        Algebra.TensorProduct.tmul_mul_tmul] using h₁c
    · simpa [IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke, IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues,
        Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul] using h₂c
    · simpa [IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke, IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues,
        hmul, hpowrat] using hcentral.symm

end

end OAI.NumberTheory.PadicHodge.ThetaParameters.FrobeniusSlope
