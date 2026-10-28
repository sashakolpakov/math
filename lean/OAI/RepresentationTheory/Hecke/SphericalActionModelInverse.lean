import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial
import OAI.Algebra.Modules.ElementaryDivisors
import Lean.Util.CollectAxioms

/-! # Spherical Action Model Inverse -/

namespace OAI.RepresentationTheory.Hecke.SphericalActionModelInverse

noncomputable section

section

/-!
# SphericalAction: native local objects

The radial functions, invertible dilation, rational spherical convolution
algebra and normalized Iwasawa constant term are concrete constructions.
The two conventions are the original substitution action and its twist by
inverse transpose; the latter will be identified with double-coset inversion.
No radial-character or Satake assertion is an interface field.
-/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial.Iwasawa

variable (q : ℕ) [Fact q.Prime]

/-- Discharge the native action's elementary-divisor input by its proof. -/
theorem cartanInput : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q] := by
  intro n π hπ L M hL hM
  let := hL
  let := hM
  exact Algebra.Modules.ElementaryDivisors.lattices_elementary_divisors π hπ L M

inductive ActingConvention
  | direct
  | inverseCoset
  deriving DecidableEq

abbrev Radial := RadialDilation.Cm.radialInput q
abbrev SphericalAlgebra := ℂ ⊗[ℚ] Theta.Geometric.SphericalGU.Spherical.SL3Hecke q

def conventionHecke (c : ActingConvention) : SphericalAlgebra q ≃ₐ[ℂ] SphericalAlgebra q :=
  match c with
  | .direct => AlgEquiv.refl
  | .inverseCoset => AlgebraicGeometry.HodgeConjecture.CMExtraction.ContragredientRadial.Local.contragredientComplexHecke q

def radialAction (c : ActingConvention) : SphericalAlgebra q →ₐ[ℂ] Module.End ℂ (Radial q) :=
  (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra.sphericalRadialComplexAlgebra q (cartanInput q)).comp (conventionHecke q c).toAlgHom

/-- Evaluate the actual normalized transform at a nonzero ordered triple. -/
def satakeEvaluation (α : Fin 3 → ℂˣ) : SphericalAlgebra q →ₐ[ℂ] ℂ :=
  (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeKernel.Iwasawa.evaluateLattice ((Units.coeHom ℂ).comp (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters.Iwasawa.torusCharacter α))).comp (AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake.Iwasawa.normalizedSatake q)

def HasSatakeParameter (χ : SphericalAlgebra q →ₐ[ℂ] ℂ) (α : Fin 3 → ℂˣ) : Prop :=
  χ = satakeEvaluation q α

/-- Permutation and a common nonzero scalar preserve multiplicities. -/
def ProjectivelyEqual (a b : Fin 3 → ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3), ∀ i, a i = c * b (σ i)

def parameterForConvention (c : ActingConvention) (e₀ : ℂ) : ℂ :=
  match c with
  | .direct => e₀
  | .inverseCoset => e₀⁻¹

/-- Full local conclusion of SphericalAction, with a constructed Satake representative. -/
def RadialSatakeConclusion (c : ActingConvention)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρV : SphericalAlgebra q →ₐ[ℂ] Module.End ℂ V)
    (Θ : Radial q →ₗ[ℂ] V) (M : ℕ) (ω : ℂ) : Prop :=
  Submodule.span ℂ
      (Set.range (fun n : ℤ => (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ n) (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.ball q 0))) = ⊤ ∧
  (∀ h b, radialAction q c h (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q b) =
    AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q (radialAction q c h b)) ∧
  ∀ χ : SphericalAlgebra q →ₐ[ℂ] ℂ,
    (∃ v : V, v ∈ LinearMap.range Θ ∧ v ≠ 0 ∧
      ∀ h, ρV h v = χ h • v) →
    ∃ e₀ : ℂ, e₀ ≠ 0 ∧ e₀ ^ M = ω ∧
      (∃ ℓ : Radial q →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
        (∀ b, ℓ (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q b) = e₀ * ℓ b) ∧
        (∀ h b, ℓ (radialAction q c h b) = χ h * ℓ b)) ∧
      ∃ α : Fin 3 → ℂˣ, HasSatakeParameter q χ α ∧
        ProjectivelyEqual (fun i => (α i : ℂ))
          ![(Real.sqrt (q : ℝ) : ℂ), (Real.sqrt (q : ℝ) : ℂ)⁻¹,
            parameterForConvention c e₀]

end

section

/-! Identify the chosen inverse-transpose automorphism with literal
double-coset inversion on every spherical kernel, rather than postulating
a convention compatibility. -/

open scoped Classical TensorProduct

variable (q : ℕ) [Fact q.Prime]

theorem active_kernel_evaluation (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (g : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    Theta.Geometric.SphericalGU.Spherical.kernel (Theta.Geometric.SphericalGU.Spherical.integralSplitGU q 1)
        (Theta.Geometric.Active.Algebra.Spherical.extendActiveOperator q (0 : Fin 1) T)
        (QuotientGroup.mk (Theta.Geometric.SphericalGU.Spherical.activeEmbedding q (0 : Fin 1) g)) =
      Theta.Geometric.SphericalGU.Spherical.kernel (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T (QuotientGroup.mk g) := by
  rw [Theta.Geometric.Active.Algebra.Spherical.extendActiveOperator_kernel]
  exact Finsupp.mapDomain_apply_of_injective (Theta.Geometric.Active.Cosets.Spherical.activeCosetMap_injective q (0 : Fin 1))
    (Theta.Geometric.SphericalGU.Spherical.kernel (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T) (QuotientGroup.mk g)

theorem activeEmbedding_transpose (g : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity.splitTranspose 1 (Theta.Geometric.SphericalGU.Spherical.activeEmbedding q (0 : Fin 1) g) =
      Theta.Geometric.SphericalGU.Spherical.activeEmbedding q (0 : Fin 1) g.transpose := by
  apply Prod.ext
  · funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    apply Units.ext
    rfl
  · rfl

theorem kernel_transpose (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (g : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    Theta.Geometric.SphericalGU.Spherical.kernel (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T (QuotientGroup.mk g.transpose) =
      Theta.Geometric.SphericalGU.Spherical.kernel (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T (QuotientGroup.mk g) := by
  rw [← active_kernel_evaluation q T g.transpose, ← active_kernel_evaluation q T g,
    ← activeEmbedding_transpose]
  exact AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity.kernel_splitTranspose 1 q (cartanInput q) _ _

/-- The inverse convention really sends the coefficient at g to that at g⁻¹. -/
theorem inverseCoset_kernel (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (g : Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    Theta.Geometric.SphericalGU.Spherical.coefficient (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphismAction.Local.contragredientHecke q T) g =
      Theta.Geometric.SphericalGU.Spherical.coefficient (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T g⁻¹ := by
  unfold Theta.Geometric.SphericalGU.Spherical.coefficient
  change Theta.Geometric.SphericalGU.Spherical.kernel _ (AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism.Local.heckeAutomorphism _ (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredientEquiv ℚ_[q])
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient_integral_iff q) T) (QuotientGroup.mk g) = _
  erw [AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism.Local.heckeAutomorphism_kernel]
  have h : AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism.Local.cosetAutomorphism (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredientEquiv ℚ_[q])
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient_integral_iff q) (QuotientGroup.mk (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient ℚ_[q] g)) =
        QuotientGroup.mk g := by
    change QuotientGroup.mk (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient ℚ_[q] (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient ℚ_[q] g)) = _
    exact congrArg QuotientGroup.mk (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient_involutive ℚ_[q] g)
  erw [← h]
  change (Finsupp.equivMapDomain
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeAutomorphism.Local.cosetAutomorphism (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredientEquiv ℚ_[q])
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Contragredient.Local.contragredient_integral_iff q))
      (Theta.Geometric.SphericalGU.Spherical.kernel (Theta.Geometric.SphericalGU.Spherical.integralSL3 q) T)) _ = _
  erw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
  exact kernel_transpose q T g⁻¹

end

/-!
# SphericalAction: conditional proof for the actual radial spherical action

The explicit inputs `hGeometricTheta` and `hRadialDilation` are the original target's covariance
and dilation-relation hypotheses, instantiated in the native local model.
The proof factors through the finite quotient by D^M - ω; it does not assume
that ker Θ is D-stable. Cyclicity and the separability of X^M - ω identify
its occurring characters. Finite Iwasawa sums then compute their normalized
Satake parameters. GL3's classification, ParabolicInduction's induction theorem and the
separate Commuting statement are not needed for this direct computation.

No statement stub is imported. The source's two acting conventions are
related by the proved `inverseCoset_kernel` identity.
-/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial.Iwasawa

theorem conventionHecke_involutive (q : ℕ) [Fact q.Prime] (c : ActingConvention) :
    Function.Involutive (conventionHecke q c) := by
  cases c with
  | direct => exact fun _ => rfl
  | inverseCoset => exact AlgebraicGeometry.HodgeConjecture.CMExtraction.ContragredientRadial.Local.contragredientComplexHecke_involutive q

theorem radial_parameter_projective (q : ℕ) [Fact q.Prime] (e : ℂˣ) :
    ProjectivelyEqual (fun i => (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters.Iwasawa.radialTorusPoint q e i : ℂ))
      ![(Real.sqrt (q : ℝ) : ℂ), (Real.sqrt (q : ℝ) : ℂ)⁻¹, (e : ℂ)] := by
  refine ⟨1, one_ne_zero, (Equiv.swap 0 2).trans (Equiv.swap 0 1), ?_⟩
  intro i
  fin_cases i <;> norm_num [AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters.Iwasawa.radialTorusPoint, AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters.Iwasawa.sqrtUnit,
    Satake.GL3TorusIwasawa.Normalization.residueSqrtUnit, Equiv.swap_apply_def, Fin.ext_iff]

/-- SphericalAction, conditional on the indicated local outputs of GeometricTheta and RadialDilation. -/
theorem projective_satake_parameters_of_radial_quotient
    (q : ℕ) [Fact q.Prime] (c : ActingConvention)
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (ρV : SphericalAlgebra q →ₐ[ℂ] Module.End ℂ V)
    (Θ : Radial q →ₗ[ℂ] V)
    (M : ℕ) (hM : 0 < M) (ω : ℂ) (hω : ‖ω‖ = 1)
    (hGeometricTheta : ∀ h b, Θ (radialAction q c h b) = ρV h (Θ b))
    (hRadialDilation : ∀ b, Θ ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b) = ω • Θ b) :
    RadialSatakeConclusion q c ρV Θ M ω := by
  refine ⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.radial_cyclic q, ?_, ?_⟩
  · intro h b
    exact AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra.sphericalRadialComplexAlgebra_dilation q (cartanInput q)
      (conventionHecke q c h) b
  · intro χ hoccurs
    obtain ⟨v, hv, hv0, hχ⟩ := hoccurs
    have hω0 : ω ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hω
      exact zero_ne_one hω
    have hrelation : ∀ b, Θ ((RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b := by
      intro b
      simpa only [AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation.dilationEquiv_pow_apply] using hRadialDilation b
    let A := conventionHecke q c
    let ρ' := ρV.comp A.toAlgHom
    let χ' := χ.comp A.toAlgHom
    have hcov : ∀ h b,
        Θ (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra.sphericalRadialComplexAlgebra q (cartanInput q) h b) = ρ' h (Θ b) := by
      intro h b
      have hh := hGeometricTheta (A h) b
      change Θ (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra.sphericalRadialComplexAlgebra q (cartanInput q) (A (A h)) b) =
        ρ' h (Θ b) at hh
      rw [conventionHecke_involutive q c h] at hh
      exact hh
    obtain ⟨e, he, hroot, hchar⟩ :=
      AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial.radial_occurring_character q (cartanInput q) ρ' Θ M hM ω hω0
        hrelation hcov χ' v hv hv0 (fun h => hχ (A h))
    have htwist : χ = (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.radialCharacter q (cartanInput q) e he).comp A.toAlgHom := by
      apply AlgHom.ext
      intro h
      have hh := DFunLike.congr_fun hchar (A h)
      change χ (A (A h)) = AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.radialCharacter q (cartanInput q) e he (A h) at hh
      rw [conventionHecke_involutive q c h] at hh
      exact hh
    refine ⟨e, he, hroot, ?_, ?_⟩
    · refine ⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.dilationFunctional q e, AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.dilationFunctional_ne_zero q e,
        AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.dilationFunctional_dilation q e he, ?_⟩
      intro h b
      change AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.dilationFunctional q e
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra.sphericalRadialComplexAlgebra q (cartanInput q) (A h) b) = _
      rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.dilationFunctional_hecke q (cartanInput q) e he]
      exact congrArg (fun z : ℂ => z * AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.dilationFunctional q e b)
        (DFunLike.congr_fun htwist h).symm
    · cases c with
      | direct =>
          refine ⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters.Iwasawa.radialTorusPoint q (Units.mk0 e he), ?_,
            radial_parameter_projective q (Units.mk0 e he)⟩
          change χ = AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake.Iwasawa.radialSatakeCharacter q (Units.mk0 e he)
          have hdirect : χ = AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters.radialCharacter q (cartanInput q) e he := by
            apply AlgHom.ext
            intro h
            exact DFunLike.congr_fun htwist h
          exact hdirect.trans (AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake.Iwasawa.radialCharacter_eq_satake q (cartanInput q) e he)
      | inverseCoset =>
          refine ⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.DualSatakeParameters.Iwasawa.dualRadialTorusPoint q (Units.mk0 e he), ?_, ?_⟩
          · change χ = AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.mk0 e he)
            exact htwist.trans
              (AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial.Iwasawa.radialCharacter_contragredient_eq_satake q (cartanInput q) e he)
          · refine ⟨1, one_ne_zero, Equiv.refl _, ?_⟩
            intro i
            fin_cases i <;> simp [AlgebraicGeometry.HodgeConjecture.CMExtraction.DualSatakeParameters.Iwasawa.dualRadialTorusPoint, AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeParameters.Iwasawa.sqrtUnit,
              Satake.GL3TorusIwasawa.Normalization.residueSqrtUnit, parameterForConvention]

end

end OAI.RepresentationTheory.Hecke.SphericalActionModelInverse
