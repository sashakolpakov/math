import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector

/-! # Intrinsic Compact Operators -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOperators.Intrinsic

noncomputable section

/-! Actual compact-place unitary operators, equal to the identity at
the distinguished place, determine the continuous native compact-frame
choices in the prescribed orthonormal coordinates. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

abbrev CompactArchMultiplicity :=
  {w : IntrinsicMultiplicityOperator.Intrinsic.ArchMultiplicity F K // w (A.enumerate A.distinguished) = 1}

def complexMultiplicity (v : Fin A.places) :
    Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inl (A.enumerate v)) →*
      Weil.AdelicSplitting.UnitaryBase.Construction.Unitary ((Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))).map (A.complex v)) :=
  Weil.AdelicSplitting.UnitaryBase.Construction.unitaryBaseChange (A.complex v).toRingHom (A.complex_star v) _

def orthonormalMultiplicity (w : IntrinsicMultiplicityOperator.Intrinsic.ArchMultiplicity F K) (v : Fin A.places) :
    (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  (A.basisP v)⁻¹ * (complexMultiplicity A v (w (A.enumerate v))).val * A.basisP v

theorem orthonormal_multiplicity_preserves (w : IntrinsicMultiplicityOperator.Intrinsic.ArchMultiplicity F K) (v : Fin A.places) :
    (orthonormalMultiplicity A w v).val.conjTranspose * IntrinsicCompactChoices.Intrinsic.multiplicityForm A v *
        (orthonormalMultiplicity A w v).val = IntrinsicCompactChoices.Intrinsic.multiplicityForm A v := by
  have h := IntrinsicUnitaryBasis.Intrinsic.unitary_in_basis _ (A.basisP v) (complexMultiplicity A v (w (A.enumerate v)))
  rw [A.formP] at h
  exact h

def nativeCompactChoice (w : CompactArchMultiplicity A) : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A where
  change := orthonormalMultiplicity A w.val
  distinguished := by
    unfold orthonormalMultiplicity
    rw [w.property,map_one]
    simp
  preserves := orthonormal_multiplicity_preserves A w.val

theorem complex_multiplicity_units_continuous (v : Fin A.places) :
    Continuous (fun w : Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inl (A.enumerate v)) =>
      (complexMultiplicity A v w).val) := by
  have hM : Continuous ((A.complex v).toRingHom.mapMatrix :
      Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v))) →
        Matrix (Fin 2) (Fin 2) ℂ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (A.complex_continuous v).comp ((continuous_apply j).comp (continuous_apply i))
  have hu : Continuous (Units.map (A.complex v).toRingHom.mapMatrix.toMonoidHom :
      (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inl (A.enumerate v))))ˣ →
        (Matrix (Fin 2) (Fin 2) ℂ)ˣ) := by
    apply Units.continuous_iff.mpr
    exact ⟨hM.comp Units.continuous_val,hM.comp Units.continuous_coe_inv⟩
  exact hu.comp continuous_subtype_val

theorem native_compact_choice_continuous : Continuous (nativeCompactChoice A) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro v
  have hw : Continuous (fun w : CompactArchMultiplicity A => w.val (A.enumerate v)) :=
    (continuous_apply (A.enumerate v)).comp continuous_subtype_val
  exact (continuous_const.mul ((complex_multiplicity_units_continuous A v).comp hw)).mul continuous_const

theorem native_compact_projectors_continuous :
    Continuous (fun w : CompactArchMultiplicity A =>
      IntrinsicCompactProjector.IntrinsicParameter.choiceParameter A (nativeCompactChoice A w)) :=
  (IntrinsicCompactProjector.Intrinsic.choice_parameter_continuous A).comp (native_compact_choice_continuous A)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOperators.Intrinsic
