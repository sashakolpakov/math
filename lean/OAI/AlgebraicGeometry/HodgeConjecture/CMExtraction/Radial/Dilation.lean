import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity

/-! # Dilation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation

noncomputable section

section

/-! A scalar relation for an invertible operator extends to all integer
powers, including negative powers, without an invariant-kernel premise. -/

open scoped Classical

theorem linear_map_zpow_relation
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (D : V ≃ₗ[ℂ] V) (Θ : V →ₗ[ℂ] W) (ω : ℂ) (hω : ω ≠ 0)
    (h : ∀ b, Θ (D b) = ω • Θ b) (n : ℤ) (b : V) :
    Θ ((D ^ n) b) = ω ^ n • Θ b := by
  have hi (x : V) : Θ (D⁻¹ x) = ω⁻¹ • Θ x := by
    have hx := congrArg (fun y : W => ω⁻¹ • y) (h (D⁻¹ x))
    have hc : D (D⁻¹ x) = x := by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    simpa only [hc, smul_smul, inv_mul_cancel₀ hω, one_smul] using hx.symm
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [show (n : ℤ) + 1 = 1 + (n : ℤ) by omega, zpow_one_add, LinearEquiv.mul_apply,
        h, ih, smul_smul, zpow_one_add₀ hω]
  | pred n ih =>
      have hp : D ^ (-(n : ℤ) - 1) = D⁻¹ * D ^ (-(n : ℤ)) := by
        rw [← zpow_neg_one, ← zpow_add]
        congr 1
        omega
      rw [hp, LinearEquiv.mul_apply, hi, ih, smul_smul]
      congr 1
      rw [zpow_sub_one₀ hω, mul_comm]

end

section

/-! The actual RadialDilation dilation relation makes the theta image finite
dimensional: the first M integer-dilation translates span it. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

theorem dilationEquiv_pow_apply (M : ℕ) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    (Cyclicity.dilationEquiv q ^ M) b = (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b := by
  induction M generalizing b with
  | zero => rfl
  | succ M ih =>
      rw [pow_succ, LinearEquiv.mul_apply, pow_succ, Module.End.mul_apply, ih]
      rfl

theorem radial_image_integer_reduction
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (ω : ℂ) (hω : ω ≠ 0)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b) (n : ℤ) :
    Θ ((Cyclicity.dilationEquiv q ^ n) (Cyclicity.ball q 0)) =
      ω ^ (n / (M : ℤ)) • Θ ((Cyclicity.dilationEquiv q ^ (n % (M : ℤ))) (Cyclicity.ball q 0)) := by
  have hblock (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) : Θ ((Cyclicity.dilationEquiv q ^ M) b) = ω • Θ b := by
    rw [dilationEquiv_pow_apply]
    exact hrelation b
  calc
    _ = Θ (((Cyclicity.dilationEquiv q ^ M) ^ (n / (M : ℤ)))
        ((Cyclicity.dilationEquiv q ^ (n % (M : ℤ))) (Cyclicity.ball q 0))) := by
      congr 1
      rw [← LinearEquiv.mul_apply, ← zpow_natCast (Cyclicity.dilationEquiv q) M,
        ← zpow_mul, ← zpow_add]
      congr 2
      simpa only [add_comm] using (Int.emod_add_mul_ediv n (M : ℤ)).symm
    _ = _ := linear_map_zpow_relation (Cyclicity.dilationEquiv q ^ M) Θ ω hω hblock _ _

theorem radial_image_finite_span
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M) (ω : ℂ) (hω : ω ≠ 0)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b) :
    LinearMap.range Θ = Submodule.span ℂ
      (Set.range (fun i : Fin M => Θ ((Cyclicity.dilationEquiv q ^ (i.val : ℤ)) (Cyclicity.ball q 0)))) := by
  let S := Submodule.span ℂ
    (Set.range (fun i : Fin M => Θ ((Cyclicity.dilationEquiv q ^ (i.val : ℤ)) (Cyclicity.ball q 0))))
  apply le_antisymm
  · have hle : Submodule.span ℂ
        (Set.range (fun n : ℤ => (Cyclicity.dilationEquiv q ^ n) (Cyclicity.ball q 0))) ≤ S.comap Θ := by
      apply Submodule.span_le.mpr
      rintro b ⟨n, rfl⟩
      change Θ ((Cyclicity.dilationEquiv q ^ n) (Cyclicity.ball q 0)) ∈ S
      rw [radial_image_integer_reduction q Θ M ω hω hrelation]
      apply S.smul_mem
      have hpos : (0 : ℤ) < M := by exact_mod_cast hM
      let i : Fin M := ⟨(n % (M : ℤ)).toNat, by
        have hn := Int.emod_lt_of_pos n hpos
        have hn0 := Int.emod_nonneg n hpos.ne'
        omega⟩
      have hi : (i.val : ℤ) = n % (M : ℤ) := by
        exact Int.toNat_of_nonneg (Int.emod_nonneg n hpos.ne')
      exact Submodule.subset_span ⟨i,
        congrArg (fun k : ℤ => Θ ((Cyclicity.dilationEquiv q ^ k) (Cyclicity.ball q 0))) hi⟩
    rw [Cyclicity.radial_cyclic] at hle
    rintro y ⟨b, rfl⟩
    exact hle (Submodule.mem_top : b ∈ (⊤ : Submodule ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)))
  · apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact ⟨_, rfl⟩

theorem radial_image_finiteDimensional
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M) (ω : ℂ) (hω : ω ≠ 0)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b) :
    FiniteDimensional ℂ (LinearMap.range Θ) := by
  rw [radial_image_finite_span q Θ M hM ω hω hrelation]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

end

/-! The finite dilation quotient is formed from the actual operator
relation. Every theta map satisfying RadialDilation factors through it. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] (M : ℕ) (ω : ℂ)

def dilationRelation : Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) := RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M - ω • 1

def dilationRelationSpace : Submodule ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) := LinearMap.range (dilationRelation q M ω)

abbrev RadialQuotient := RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q ⧸ dilationRelationSpace q M ω

def radialQuotientMap : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RadialQuotient q M ω :=
  (dilationRelationSpace q M ω).mkQ

theorem radialQuotientMap_relation (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    radialQuotientMap q M ω ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • radialQuotientMap q M ω b := by
  have hzero : radialQuotientMap q M ω (dilationRelation q M ω b) = 0 := by
    apply LinearMap.mem_ker.mp
    change dilationRelation q M ω b ∈ LinearMap.ker (dilationRelationSpace q M ω).mkQ
    rw [Submodule.ker_mkQ]
    exact ⟨b, rfl⟩
  change radialQuotientMap q M ω ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b - ω • b) = 0 at hzero
  rw [map_sub, map_smul] at hzero
  exact sub_eq_zero.mp hzero

theorem radialQuotient_finiteDimensional (hM : 0 < M) (hω : ω ≠ 0) :
    FiniteDimensional ℂ (RadialQuotient q M ω) := by
  let := radial_image_finiteDimensional q (radialQuotientMap q M ω) M hM ω hω
    (radialQuotientMap_relation q M ω)
  apply Module.Finite.of_surjective (LinearMap.range (radialQuotientMap q M ω)).subtype
  intro x
  obtain ⟨b, hb⟩ := (dilationRelationSpace q M ω).mkQ_surjective x
  exact ⟨⟨x, ⟨b, hb⟩⟩, rfl⟩

theorem dilationRelationSpace_le_ker
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b) :
    dilationRelationSpace q M ω ≤ LinearMap.ker Θ := by
  rintro x ⟨b, rfl⟩
  change Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b - ω • b) = 0
  rw [map_sub, map_smul, hrelation, sub_self]

def radialQuotientLift
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b) :
    RadialQuotient q M ω →ₗ[ℂ] W :=
  (dilationRelationSpace q M ω).liftQ Θ (dilationRelationSpace_le_ker q M ω Θ hrelation)

theorem radialQuotientLift_comp
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b) :
    (radialQuotientLift q M ω Θ hrelation).comp (radialQuotientMap q M ω) = Θ :=
  Submodule.liftQ_mkQ _ _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation
