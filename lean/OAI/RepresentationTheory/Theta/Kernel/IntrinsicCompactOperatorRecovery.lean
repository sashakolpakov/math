import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOperators
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryFieldEquiv

/-! # Intrinsic Compact Operator Recovery -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOperatorRecovery.Intrinsic

noncomputable section

/-! Every native compact-frame choice is represented by an actual
compact-place multiplicity operator. Both field and basis changes are
invertible, and the distinguished operator is exactly the identity. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOperators.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryBasis.IntrinsicEquiv OAI.RepresentationTheory.Theta.Kernel.IntrinsicUnitaryFieldEquiv.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def localMultiplicityEquiv (v : Fin A.places) :
    Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inl (A.enumerate v)) ≃*
      Weil.AdelicSplitting.UnitaryBase.Construction.Unitary ((A.basisP v).val.conjTranspose *
        ((Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))).map (A.complex v)) * (A.basisP v).val) :=
  (IntrinsicUnitaryFieldEquiv.Intrinsic.unitaryFieldEquiv (A.complex v) (A.complex_star v) _).trans
    (IntrinsicUnitaryBasis.IntrinsicEquiv.unitaryBasisEquiv _ (A.basisP v))

def localChoiceUnitary (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (v : Fin A.places) :
    Weil.AdelicSplitting.UnitaryBase.Construction.Unitary ((A.basisP v).val.conjTranspose *
      ((Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))).map (A.complex v)) * (A.basisP v).val) :=
  ⟨p.change v,by rw [A.formP]; exact p.preserves v⟩

def operatorsOfChoice (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) : IntrinsicCompactOperators.Intrinsic.CompactArchMultiplicity A :=
  ⟨Equiv.piCongrLeft (fun v => Weil.AdelicSplitting.Integral.Construction.LocalUnitary F K.val (.inl v)) A.enumerate
      (fun v => (localMultiplicityEquiv A v).symm (localChoiceUnitary A p v)),by
    rw [Equiv.piCongrLeft_apply_apply]
    have h : localChoiceUnitary A p A.distinguished = 1 :=
      Subtype.ext p.distinguished
    rw [h,map_one]⟩

theorem compact_choice_ext {p q : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A} (h : p.change = q.change) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem native_compact_choice_recovery (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) :
    IntrinsicCompactOperators.Intrinsic.nativeCompactChoice A (operatorsOfChoice A p) = p := by
  apply compact_choice_ext
  funext v
  change ((localMultiplicityEquiv A v) ((operatorsOfChoice A p).val (A.enumerate v))).val = p.change v
  simp only [operatorsOfChoice,Equiv.piCongrLeft_apply_apply,MulEquiv.apply_symm_apply]
  rfl

theorem native_compact_choice_surjective : Function.Surjective (IntrinsicCompactOperators.Intrinsic.nativeCompactChoice A) :=
  fun p => ⟨operatorsOfChoice A p,native_compact_choice_recovery A p⟩

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOperatorRecovery.Intrinsic
