import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations
import OAI.ArithmeticGeometry.Models.SpreadingOut.AlgebraicSpecialization
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Smooth.Kaehler

/-! # Kaehler Point Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection

noncomputable section

/-! On a smooth integral affine complex scheme, point derivations
faithfully detect actual algebraic Kähler differentials. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations

variable {R : Type} [CommRing R] [Algebra ℂ R]

def pointDerivationAsDerivation (x : R →ₐ[ℂ] ℂ) (D : AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations x) :
    let : Algebra R ℂ := x.toAlgebra
    Derivation ℂ R ℂ := by
  let : Algebra R ℂ := x.toAlgebra
  exact {
    toLinearMap := D.val
    map_one_eq_zero' := D.property.1
    leibniz' := by
      intro a b
      exact D.property.2 a b }

def pointKaehlerValue (x : R →ₐ[ℂ] ℂ) (D : AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations x) :
    KaehlerDifferential ℂ R →ₗ[ℂ] ℂ := by
  let : Algebra R ℂ := x.toAlgebra
  have : IsScalarTower ℂ R ℂ := IsScalarTower.of_algebraMap_eq (fun c => (x.commutes c).symm)
  exact (pointDerivationAsDerivation x D).liftKaehlerDifferential.restrictScalars ℂ

theorem pointKaehlerValue_D (x : R →ₐ[ℂ] ℂ) (D : AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations x) (a : R) :
    pointKaehlerValue x D (KaehlerDifferential.D ℂ R a) = D.val a := by
  let : Algebra R ℂ := x.toAlgebra
  exact (pointDerivationAsDerivation x D).liftKaehlerDifferential_comp_D a

theorem pointKaehlerValue_smul (x : R →ₐ[ℂ] ℂ) (D : AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations x)
    (r : R) (ω : KaehlerDifferential ℂ R) :
    pointKaehlerValue x D (r • ω) = x r * pointKaehlerValue x D ω := by
  let : Algebra R ℂ := x.toAlgebra
  have : IsScalarTower ℂ R ℂ := IsScalarTower.of_algebraMap_eq (fun c => (x.commutes c).symm)
  change (pointDerivationAsDerivation x D).liftKaehlerDifferential (r • ω) =
    r • (pointDerivationAsDerivation x D).liftKaehlerDifferential ω
  exact (pointDerivationAsDerivation x D).liftKaehlerDifferential.map_smul r ω

def pointDerivationOfKaehlerDual (x : R →ₐ[ℂ] ℂ)
    (f : KaehlerDifferential ℂ R →ₗ[R] R) : AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations x := by
  let d : R →ₗ[ℂ] ℂ := x.toLinearMap.comp ((f.restrictScalars ℂ).comp (KaehlerDifferential.D ℂ R).toLinearMap)
  refine ⟨d, ?_, ?_⟩
  · change x (f (KaehlerDifferential.D ℂ R 1)) = 0
    rw [Derivation.map_one_eq_zero, map_zero, map_zero]
  · intro a b
    change x (f (KaehlerDifferential.D ℂ R (a * b))) =
      x a * x (f (KaehlerDifferential.D ℂ R b)) + x b * x (f (KaehlerDifferential.D ℂ R a))
    rw [Derivation.leibniz, map_add, map_smul, map_smul, map_add]
    simp only [smul_eq_mul, map_mul]

theorem pointKaehlerValue_dual (x : R →ₐ[ℂ] ℂ) (f : KaehlerDifferential ℂ R →ₗ[R] R)
    (ω : KaehlerDifferential ℂ R) :
    pointKaehlerValue x (pointDerivationOfKaehlerDual x f) ω = x (f ω) := by
  have hspan : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D ℂ R)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hspan using Submodule.span_induction with
  | mem ω h =>
    obtain ⟨a, rfl⟩ := h
    rw [pointKaehlerValue_D]
    rfl
  | zero => simp only [map_zero]
  | add a b ha hb hea heb => simp only [map_add, hea, heb]
  | smul r a ha hea =>
    rw [pointKaehlerValue_smul, hea, map_smul, smul_eq_mul, map_mul]

theorem kaehler_eq_zero_of_pointDerivations [IsDomain R] [Algebra.Smooth ℂ R]
    (ω : KaehlerDifferential ℂ R)
    (hω : ∀ (x : R →ₐ[ℂ] ℂ) (D : AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations x), pointKaehlerValue x D ω = 0) : ω = 0 := by
  by_contra he
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero R he
  obtain ⟨x, hx⟩ := ArithmeticGeometry.Models.SpreadingOut.AlgebraicSpecialization.Construction.finiteType_specialization_nonzero ℂ R hf
  let c : AlgebraicClosure ℂ →ₐ[ℂ] ℂ := IsAlgClosed.lift
  let y : R →ₐ[ℂ] ℂ := c.comp x
  have h := hω y (pointDerivationOfKaehlerDual y f)
  rw [pointKaehlerValue_dual] at h
  exact hx (c.injective (h.trans c.map_zero.symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection
