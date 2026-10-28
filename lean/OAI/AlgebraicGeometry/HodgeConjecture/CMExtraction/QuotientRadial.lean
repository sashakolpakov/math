import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientDilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CyclicOperators

/-! # Quotient Radial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial

noncomputable section

section

/-! Radial eigenfunctionals descend to the actual finite quotient.
The quotient is cyclic under the induced dilation. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] (M : ℕ) (ω e : ℂ)

theorem dilationFunctional_power_relation (he : e ≠ 0) (hroot : e ^ M = ω) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    Radial.Characters.dilationFunctional q e ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Radial.Characters.dilationFunctional q e b := by
  have h := Radial.Dilation.linear_map_zpow_relation (Radial.Cyclicity.dilationEquiv q) (Radial.Characters.dilationFunctional q e) e he
    (Radial.Characters.dilationFunctional_dilation q e he) (M : ℤ) b
  simpa only [zpow_natCast, Radial.Dilation.dilationEquiv_pow_apply, hroot] using h

def quotientFunctional (he : e ≠ 0) (hroot : e ^ M = ω) : Radial.Dilation.RadialQuotient q M ω →ₗ[ℂ] ℂ :=
  Radial.Dilation.radialQuotientLift q M ω (Radial.Characters.dilationFunctional q e) (dilationFunctional_power_relation q M ω e he hroot)

theorem quotientFunctional_mkQ (he : e ≠ 0) (hroot : e ^ M = ω) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    quotientFunctional q M ω e he hroot (Radial.Dilation.radialQuotientMap q M ω b) = Radial.Characters.dilationFunctional q e b := rfl

theorem quotientFunctional_unit_ball (he : e ≠ 0) (hroot : e ^ M = ω) :
    quotientFunctional q M ω e he hroot (Radial.Dilation.radialQuotientMap q M ω (Radial.Cyclicity.ball q 0)) = 1 :=
  Radial.Characters.dilationFunctional_unit_ball q e

theorem quotientFunctional_dilation (he : e ≠ 0) (hroot : e ^ M = ω)
    (x : Radial.Dilation.RadialQuotient q M ω) :
    quotientFunctional q M ω e he hroot (QuotientDilation.Radial.quotientDilation q M ω x) =
      e * quotientFunctional q M ω e he hroot x := by
  obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
  rw [show (Radial.Dilation.dilationRelationSpace q M ω).mkQ b = Radial.Dilation.radialQuotientMap q M ω b from rfl,
    QuotientDilation.Radial.quotientDilation_mkQ, quotientFunctional_mkQ, quotientFunctional_mkQ]
  exact Radial.Characters.dilationFunctional_dilation q e he b

theorem quotientFunctional_hecke
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (he : e ≠ 0) (hroot : e ^ M = ω)
    (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (x : Radial.Dilation.RadialQuotient q M ω) :
    quotientFunctional q M ω e he hroot (QuotientDilation.Radial.quotientHeckeAlgebra q M ω hElementaryDivisors T x) =
      Radial.Characters.radialCharacter q hElementaryDivisors e he T * quotientFunctional q M ω e he hroot x := by
  obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
  exact Radial.Characters.dilationFunctional_hecke q hElementaryDivisors e he T b

theorem quotientDilation_cyclic (hM : 0 < M) (hω : ω ≠ 0) :
    Submodule.span ℂ (Set.range (fun i : Fin M =>
      (QuotientDilation.Radial.quotientDilation q M ω ^ i.val) (Radial.Dilation.radialQuotientMap q M ω (Radial.Cyclicity.ball q 0)))) = ⊤ := by
  have hspan := Radial.Dilation.radial_image_finite_span q (Radial.Dilation.radialQuotientMap q M ω) M hM ω hω
    (Radial.Dilation.radialQuotientMap_relation q M ω)
  have hrange : LinearMap.range (Radial.Dilation.radialQuotientMap q M ω) = ⊤ := Submodule.range_mkQ _
  have he : (fun i : Fin M => (QuotientDilation.Radial.quotientDilation q M ω ^ i.val)
      (Radial.Dilation.radialQuotientMap q M ω (Radial.Cyclicity.ball q 0))) =
      (fun i : Fin M => Radial.Dilation.radialQuotientMap q M ω ((Radial.Cyclicity.dilationEquiv q ^ (i.val : ℤ)) (Radial.Cyclicity.ball q 0))) := by
    funext i
    rw [zpow_natCast, Radial.Dilation.dilationEquiv_pow_apply, QuotientDilation.Radial.quotientDilation_pow_mkQ]
  rw [he]
  exact hspan.symm.trans hrange

end

section

/-! The actual Hecke action on each dilation eigenspace has the
constructed radial character. No Satake triple is assumed here. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] (M : ℕ) (ω : ℂ)

theorem quotient_eigenvalue_root (e : ℂ) (x : Radial.Dilation.RadialQuotient q M ω)
    (hx : QuotientDilation.Radial.quotientDilation q M ω x = e • x) (hne : x ≠ 0) : e ^ M = ω := by
  have hpow : e ^ M • x = ω • x :=
    (CyclicOperators.Radial.end_pow_of_eigenvector (QuotientDilation.Radial.quotientDilation q M ω) e x hx M).symm.trans
      (congrArg (fun A : Module.End ℂ (Radial.Dilation.RadialQuotient q M ω) => A x) (QuotientDilation.Radial.quotientDilation_power q M ω))
  have hz : (e ^ M - ω) • x = 0 := by rw [sub_smul, hpow, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hne)

theorem quotient_hecke_on_eigenvector
    (hM : 0 < M) (hω : ω ≠ 0)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (e : ℂ) (he : e ≠ 0) (hroot : e ^ M = ω)
    (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (x : Radial.Dilation.RadialQuotient q M ω)
    (hx : QuotientDilation.Radial.quotientDilation q M ω x = e • x) :
    QuotientDilation.Radial.quotientHeckeAlgebra q M ω hElementaryDivisors T x = Radial.Characters.radialCharacter q hElementaryDivisors e he T • x := by
  let D := QuotientDilation.Radial.quotientDilation q M ω
  let ℓ := quotientFunctional q M ω e he hroot
  let v := Radial.Dilation.radialQuotientMap q M ω (Radial.Cyclicity.ball q 0)
  have hℓv : ℓ v = 1 := quotientFunctional_unit_ball q M ω e he hroot
  obtain ⟨c, hc⟩ := CyclicOperators.Radial.cyclic_commuting_operator D (QuotientDilation.Radial.quotientHeckeAlgebra q M ω hElementaryDivisors T) v M
    (quotientDilation_cyclic q M ω hM hω) (QuotientDilation.Radial.quotientHecke_dilation_commute q M ω hElementaryDivisors T)
  have hℓ (n : ℕ) : ℓ ((D ^ n) v) = e ^ n := by
    have h := CyclicOperators.Radial.linear_map_pow_relation D ℓ e (quotientFunctional_dilation q M ω e he hroot) n v
    simpa only [hℓv, smul_eq_mul, mul_one] using h
  have hchar : ∑ i : Fin M, c i * e ^ i.val = Radial.Characters.radialCharacter q hElementaryDivisors e he T := by
    have h := congrArg (fun A : Module.End ℂ (Radial.Dilation.RadialQuotient q M ω) => ℓ (A v)) hc
    change quotientFunctional q M ω e he hroot
      (QuotientDilation.Radial.quotientHeckeAlgebra q M ω hElementaryDivisors T v) = _ at h
    rw [quotientFunctional_hecke, quotientFunctional_unit_ball, mul_one] at h
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hℓ, smul_eq_mul] using h.symm
  rw [hc, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, CyclicOperators.Radial.end_pow_of_eigenvector D e x hx, smul_smul]
  rw [← Finset.sum_smul, hchar]

end

/-! Every character occurring in a theta image satisfying the actual
dilation relation comes from a root of that relation. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]
  (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  (ρ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] Module.End ℂ W)

def jointCharacterSpace (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) → ℂ) : Submodule ℂ W :=
  ⨅ T, (ρ T).maxGenEigenspace (χ T)

include hElementaryDivisors in
theorem jointCharacterSpace_independent : iSupIndep (jointCharacterSpace q ρ) := by
  apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
  intro T U
  apply Module.End.mapsTo_maxGenEigenspace_of_comm
  have h : ρ T * ρ U = ρ U * ρ T :=
    (ρ.map_mul T U).symm.trans
      ((congrArg ρ (Radial.Algebra.complex_hecke_commutative q hElementaryDivisors T U)).trans (ρ.map_mul U T))
  exact h.symm

theorem eigenvector_mem_jointCharacterSpace
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) → ℂ) (x : W)
    (hx : ∀ T, ρ T x = χ T • x) : x ∈ jointCharacterSpace q ρ χ := by
  apply (Module.End.mem_iInf_maxGenEigenspace_iff (fun T => ρ T) χ x).mpr
  intro T
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx, sub_self]

theorem radial_generalized_occurring_character
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M) (ω : ℂ) (hω : ω ≠ 0)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b)
    (hHecke : ∀ T b, Θ (Radial.Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (w : W) (hw : w ∈ LinearMap.range Θ) (hne : w ≠ 0)
    (hχ : w ∈ jointCharacterSpace q ρ (fun T => χ T)) :
    ∃ (e : ℂ) (he : e ≠ 0), e ^ M = ω ∧ χ = Radial.Characters.radialCharacter q hElementaryDivisors e he := by
  let C : Set ((ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) → ℂ) :=
    {μ | ∃ (e : ℂ) (he : e ≠ 0), e ^ M = ω ∧
      (fun T => Radial.Characters.radialCharacter q hElementaryDivisors e he T) = μ}
  let S : Submodule ℂ W := ⨆ μ ∈ C, jointCharacterSpace q ρ μ
  let F := Radial.Dilation.radialQuotientLift q M ω Θ hrelation
  let := Radial.Dilation.radialQuotient_finiteDimensional q M ω hM hω
  have hcover : (⊤ : Submodule ℂ (Radial.Dilation.RadialQuotient q M ω)) ≤ S.comap F := by
    rw [← (QuotientDilation.Radial.quotientDilation_semisimple q M ω hM hω).iSup_eigenspace_eq_top]
    apply iSup_le
    intro e x hx
    change F x ∈ S
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
      exact S.zero_mem
    have heigen : QuotientDilation.Radial.quotientDilation q M ω x = e • x := Module.End.mem_eigenspace_iff.mp hx
    have hroot := quotient_eigenvalue_root q M ω e x heigen hx0
    have he : e ≠ 0 := by
      intro he0
      apply hω
      rw [← hroot, he0, zero_pow hM.ne']
    have hmem : F x ∈ jointCharacterSpace q ρ (fun T => Radial.Characters.radialCharacter q hElementaryDivisors e he T) := by
      apply eigenvector_mem_jointCharacterSpace
      intro T
      rw [← QuotientDilation.Radial.radialQuotientLift_hecke q M ω hElementaryDivisors ρ Θ hrelation hHecke T x]
      rw [quotient_hecke_on_eigenvector q M ω hM hω hElementaryDivisors e he hroot T x heigen, map_smul]
    have hC : (fun T => Radial.Characters.radialCharacter q hElementaryDivisors e he T) ∈ C := ⟨e, he, hroot, rfl⟩
    have hle : jointCharacterSpace q ρ (fun T => Radial.Characters.radialCharacter q hElementaryDivisors e he T) ≤ S :=
      le_iSup_of_le (fun T => Radial.Characters.radialCharacter q hElementaryDivisors e he T) (le_iSup_of_le hC le_rfl)
    exact hle hmem
  have hwS : w ∈ S := by
    obtain ⟨b, rfl⟩ := hw
    exact hcover (Submodule.mem_top : Radial.Dilation.radialQuotientMap q M ω b ∈
      (⊤ : Submodule ℂ (Radial.Dilation.RadialQuotient q M ω)))
  have hχC : (fun T => χ T) ∈ C := by
    by_contra hnot
    have hd := (jointCharacterSpace_independent q hElementaryDivisors ρ).disjoint_biSup hnot
    have hm : w ∈ jointCharacterSpace q ρ (fun T => χ T) ⊓ S := ⟨hχ, hwS⟩
    have heq : jointCharacterSpace q ρ (fun T => χ T) ⊓ S = ⊥ := hd.eq_bot
    rw [heq] at hm
    exact hne hm
  obtain ⟨e, he, hroot, hchar⟩ := hχC
  refine ⟨e, he, hroot, ?_⟩
  apply AlgHom.ext
  intro T
  exact (congrFun hchar T).symm

theorem radial_occurring_character
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M) (ω : ℂ) (hω : ω ≠ 0)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b)
    (hHecke : ∀ T b, Θ (Radial.Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (w : W) (hw : w ∈ LinearMap.range Θ) (hne : w ≠ 0)
    (hχ : ∀ T, ρ T w = χ T • w) :
    ∃ (e : ℂ) (he : e ≠ 0), e ^ M = ω ∧ χ = Radial.Characters.radialCharacter q hElementaryDivisors e he :=
  radial_generalized_occurring_character q hElementaryDivisors ρ Θ M hM ω hω hrelation hHecke χ w hw hne
    (eigenvector_mem_jointCharacterSpace q ρ (fun T => χ T) w hχ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial
