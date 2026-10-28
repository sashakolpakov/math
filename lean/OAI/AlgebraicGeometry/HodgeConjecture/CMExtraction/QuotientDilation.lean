import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra

/-! # Quotient Dilation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientDilation.Radial

noncomputable section

section

/-! Dilation acts on its actual finite quotient and is semisimple there.
The polynomial X^M-ω is separable in characteristic zero. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] (M : ℕ) (ω : ℂ)

theorem dilationRelationSpace_invariant (A : Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q))
    (hA : Commute A (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q)) :
    Radial.Dilation.dilationRelationSpace q M ω ≤ (Radial.Dilation.dilationRelationSpace q M ω).comap A := by
  rintro x ⟨b, rfl⟩
  refine ⟨A b, ?_⟩
  change (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) (A b) - ω • A b = A ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b - ω • b)
  rw [map_sub, map_smul]
  congr 1
  exact (congrArg (fun f : Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) => f b) (hA.pow_right M).eq).symm

def quotientDilation : Module.End ℂ (Radial.Dilation.RadialQuotient q M ω) :=
  (Radial.Dilation.dilationRelationSpace q M ω).mapQ (Radial.Dilation.dilationRelationSpace q M ω) (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q)
    (dilationRelationSpace_invariant q M ω (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q) (Commute.refl _))

theorem quotientDilation_mkQ (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    quotientDilation q M ω (Radial.Dilation.radialQuotientMap q M ω b) =
      Radial.Dilation.radialQuotientMap q M ω (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q b) := rfl

theorem quotientDilation_pow_mkQ (n : ℕ) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    (quotientDilation q M ω ^ n) (Radial.Dilation.radialQuotientMap q M ω b) =
      Radial.Dilation.radialQuotientMap q M ω ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ n) b) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, quotientDilation_mkQ, ih,
        pow_succ, Module.End.mul_apply]

theorem quotientDilation_power : quotientDilation q M ω ^ M = ω • 1 := by
  apply LinearMap.ext
  intro x
  obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
  exact (quotientDilation_pow_mkQ q M ω M b).trans (Radial.Dilation.radialQuotientMap_relation q M ω b)

theorem quotientDilation_semisimple (hM : 0 < M) (hω : ω ≠ 0) :
    (quotientDilation q M ω).IsSemisimple := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C ω (by exact_mod_cast hM.ne') hω).squarefree
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    quotientDilation_power, Algebra.algebraMap_eq_smul_one, sub_self]

end

/-! The actual complex Hecke action descends to the same finite dilation
quotient through which theta factors. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime] (M : ℕ) (ω : ℂ)
  (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])

theorem sphericalRadialAlgebra_commutes_dilation (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    Commute (Radial.Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T) (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q) := by
  apply LinearMap.ext
  intro b
  exact Radial.Algebra.sphericalRadialComplexAlgebra_dilation q hElementaryDivisors T b

def quotientHeckeOperator (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    Module.End ℂ (Radial.Dilation.RadialQuotient q M ω) :=
  (Radial.Dilation.dilationRelationSpace q M ω).mapQ (Radial.Dilation.dilationRelationSpace q M ω)
    (Radial.Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T)
    (dilationRelationSpace_invariant q M ω _ (sphericalRadialAlgebra_commutes_dilation q hElementaryDivisors T))

theorem quotientHeckeOperator_mkQ (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    quotientHeckeOperator q M ω hElementaryDivisors T (Radial.Dilation.radialQuotientMap q M ω b) =
      Radial.Dilation.radialQuotientMap q M ω (Radial.Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) := rfl

def quotientHeckeAlgebra : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ]
    Module.End ℂ (Radial.Dilation.RadialQuotient q M ω) where
  toFun := quotientHeckeOperator q M ω hElementaryDivisors
  map_zero' := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
    change quotientHeckeOperator q M ω hElementaryDivisors 0 (Radial.Dilation.radialQuotientMap q M ω b) = 0
    rw [quotientHeckeOperator_mkQ, map_zero, LinearMap.zero_apply, map_zero]
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
    change quotientHeckeOperator q M ω hElementaryDivisors 1 (Radial.Dilation.radialQuotientMap q M ω b) = _
    rw [quotientHeckeOperator_mkQ, map_one]
    rfl
  map_add' T U := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
    change quotientHeckeOperator q M ω hElementaryDivisors (T + U) (Radial.Dilation.radialQuotientMap q M ω b) =
      quotientHeckeOperator q M ω hElementaryDivisors T (Radial.Dilation.radialQuotientMap q M ω b) +
        quotientHeckeOperator q M ω hElementaryDivisors U (Radial.Dilation.radialQuotientMap q M ω b)
    simp only [quotientHeckeOperator_mkQ, map_add, LinearMap.add_apply]
  map_mul' T U := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
    change quotientHeckeOperator q M ω hElementaryDivisors (T * U) (Radial.Dilation.radialQuotientMap q M ω b) =
      quotientHeckeOperator q M ω hElementaryDivisors T
        (quotientHeckeOperator q M ω hElementaryDivisors U (Radial.Dilation.radialQuotientMap q M ω b))
    simp only [quotientHeckeOperator_mkQ, map_mul, Module.End.mul_apply]
  commutes' c := by
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
    change quotientHeckeOperator q M ω hElementaryDivisors ((algebraMap ℂ _) c) (Radial.Dilation.radialQuotientMap q M ω b) =
      c • Radial.Dilation.radialQuotientMap q M ω b
    rw [quotientHeckeOperator_mkQ, AlgHom.commutes]
    exact (Radial.Dilation.radialQuotientMap q M ω).map_smul c b

theorem quotientHecke_dilation_commute (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    Commute (quotientHeckeAlgebra q M ω hElementaryDivisors T) (quotientDilation q M ω) := by
  apply LinearMap.ext
  intro x
  obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
  change quotientHeckeOperator q M ω hElementaryDivisors T
    (quotientDilation q M ω (Radial.Dilation.radialQuotientMap q M ω b)) =
      quotientDilation q M ω
        (quotientHeckeOperator q M ω hElementaryDivisors T (Radial.Dilation.radialQuotientMap q M ω b))
  rw [quotientDilation_mkQ, quotientHeckeOperator_mkQ, quotientHeckeOperator_mkQ, quotientDilation_mkQ]
  exact congrArg (Radial.Dilation.radialQuotientMap q M ω) (Radial.Algebra.sphericalRadialComplexAlgebra_dilation q hElementaryDivisors T b)

theorem radialQuotientLift_hecke
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] Module.End ℂ W)
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b)
    (hHecke : ∀ T b, Θ (Radial.Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (x : Radial.Dilation.RadialQuotient q M ω) :
    Radial.Dilation.radialQuotientLift q M ω Θ hrelation (quotientHeckeAlgebra q M ω hElementaryDivisors T x) =
      ρ T (Radial.Dilation.radialQuotientLift q M ω Θ hrelation x) := by
  obtain ⟨b, rfl⟩ := (Radial.Dilation.dilationRelationSpace q M ω).mkQ_surjective x
  exact hHecke T b

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientDilation.Radial
