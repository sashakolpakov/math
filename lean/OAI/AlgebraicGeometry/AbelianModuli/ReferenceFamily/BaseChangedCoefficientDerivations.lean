import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Base Changed Coefficient Derivations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseChangedCoefficientDerivations

noncomputable section

/-! Relative derivations extend to the actual base-changed algebra
through the canonical cotangent base-change equivalence. Their values on
the original affine algebra are retained. -/

open scoped TensorProduct

variable (R S A B C : Type) [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra R C]
    [Algebra S B] [Algebra S C] [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower R S B] [IsScalarTower R A B] [IsScalarTower R S C]
    [IsScalarTower R A C] [IsScalarTower S B C] [IsScalarTower A B C]
    [Algebra.IsPushout R S A B]

omit [CommRing C] [Algebra R C] [Algebra S C] [Algebra A C] [Algebra B C]
    [IsScalarTower R S C] [IsScalarTower R A C] [IsScalarTower S B C] [IsScalarTower A B C] in
theorem tensorKaehlerEquiv_symm_D_algebraMap (a : A) :
    (KaehlerDifferential.tensorKaehlerEquiv R S A B).symm
      (KaehlerDifferential.D S B (algebraMap A B a)) =
        (1 : B) ⊗ₜ[A] KaehlerDifferential.D R A a := by
  apply (KaehlerDifferential.tensorKaehlerEquiv R S A B).symm_apply_eq.mpr
  simpa only [one_smul] using (KaehlerDifferential.tensorKaehlerEquiv_tmul_D R S A B (1 : B) a).symm

def baseChangedCoefficientDerivation (d : Derivation R A C) : Derivation S B C :=
  KaehlerDifferential.linearMapEquivDerivation S B
    ((d.liftKaehlerDifferential.liftBaseChange B).comp
      (KaehlerDifferential.tensorKaehlerEquiv R S A B).symm.toLinearMap)

omit [IsScalarTower R S C] in
theorem baseChangedCoefficientDerivation_algebraMap (d : Derivation R A C) (a : A) :
    baseChangedCoefficientDerivation R S A B C d (algebraMap A B a) = d a := by
  change d.liftKaehlerDifferential.liftBaseChange B
    ((KaehlerDifferential.tensorKaehlerEquiv R S A B).symm
      (KaehlerDifferential.D S B (algebraMap A B a))) = d a
  rw [tensorKaehlerEquiv_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]

include R in
theorem baseChangedCoefficientDerivation_ext (d e : Derivation S B C)
    (h : ∀ a : A, d (algebraMap A B a) = e (algebraMap A B a)) : d = e := by
  have hA : (d.liftKaehlerDifferential.restrictScalars A).comp (KaehlerDifferential.map R S A B) =
      (e.liftKaehlerDifferential.restrictScalars A).comp (KaehlerDifferential.map R S A B) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro a
    change d.liftKaehlerDifferential
        (KaehlerDifferential.map R S A B (KaehlerDifferential.D R A a)) =
      e.liftKaehlerDifferential
        (KaehlerDifferential.map R S A B (KaehlerDifferential.D R A a))
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h a
  have hS : d.liftKaehlerDifferential.restrictScalars S = e.liftKaehlerDifferential.restrictScalars S :=
    (KaehlerDifferential.isBaseChange R S A B).algHom_ext' _ _
      (congrArg (fun f : KaehlerDifferential R A →ₗ[A] C => f.restrictScalars R) hA)
  apply Derivation.ext
  intro b
  have hb := LinearMap.congr_fun hS (KaehlerDifferential.D S B b)
  change d.liftKaehlerDifferential (KaehlerDifferential.D S B b) =
    e.liftKaehlerDifferential (KaehlerDifferential.D S B b) at hb
  simpa only [Derivation.liftKaehlerDifferential_comp_D] using hb

def baseChangedCoefficientDerivationLinear : Derivation R A C →ₗ[C] Derivation S B C where
  toFun := baseChangedCoefficientDerivation R S A B C
  map_add' d e := by
    apply baseChangedCoefficientDerivation_ext R S A B C
    intro a
    simp only [baseChangedCoefficientDerivation_algebraMap, Derivation.add_apply]
  map_smul' c d := by
    apply baseChangedCoefficientDerivation_ext R S A B C
    intro a
    simp only [baseChangedCoefficientDerivation_algebraMap, Derivation.smul_apply, RingHom.id_apply]

def baseChangedCoefficientDerivationRestrict : Derivation S B C →ₗ[C] Derivation R A C where
  toFun d := (d.restrictScalars R).compAlgebraMap A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def baseChangedCoefficientDerivationEquiv : Derivation R A C ≃ₗ[C] Derivation S B C where
  __ := baseChangedCoefficientDerivationLinear R S A B C
  invFun := baseChangedCoefficientDerivationRestrict R S A B C
  left_inv d := by
    apply Derivation.ext
    intro a
    exact baseChangedCoefficientDerivation_algebraMap R S A B C d a
  right_inv d := by
    apply baseChangedCoefficientDerivation_ext R S A B C
    intro a
    exact baseChangedCoefficientDerivation_algebraMap R S A B C
      (baseChangedCoefficientDerivationRestrict R S A B C d) a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseChangedCoefficientDerivations
