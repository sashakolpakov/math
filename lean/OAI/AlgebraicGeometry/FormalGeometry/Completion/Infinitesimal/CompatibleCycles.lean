import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ZeroCycleTransitions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ClopenSections

/-! # Compatible Cycles -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CompatibleCycles.Construction

noncomputable section

/-! Actual compatible infinitesimal global sections are compatible reduced native zero-cycles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The zeroth adic quotient of any module has just one element. -/
theorem adicZerothQuotient_eq {M : Type u} [AddCommGroup M] [Module R M]
    (x y : M ⧸ (I ^ 0 • ⊤ : Submodule R M)) : x = y := by
  apply (Submodule.Quotient.equiv (I ^ 0 • ⊤) ⊤ (.refl R M) (by simp)).injective
  exact Subsingleton.elim _ _

variable {X : Scheme.{u}} [X.IsSeparated] (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

/-- Insert the trivial zeroth quotient into the actual infinitesimal section coordinates. -/
def infinitesimalSectionCycleSequence (s : ClopenSections.Construction.infinitesimalGlobalSections I f) :
    ∀ n, (RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X 0 ⧸
      (I ^ n • ⊤ : Submodule R ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X 0))
  | 0 => 0
  | n + 1 => (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n (s.val n)).val

theorem infinitesimalSectionCycleSequence_compatible (s : ClopenSections.Construction.infinitesimalGlobalSections I f)
    {m n : ℕ} (h : m ≤ n) :
    AdicCompletion.transitionMap I ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X 0) h
      (infinitesimalSectionCycleSequence I f U hU hcover s n) =
        infinitesimalSectionCycleSequence I f U hU hcover s m := by
  symm
  apply Submodule.eq_factor_of_eq_factor_succ
    (fun _ _ h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)) _ _ h
  intro k
  cases k with
  | zero => exact adicZerothQuotient_eq I _ _
  | succ k =>
    have ht := congrArg Subtype.val
      (ZeroCycleTransitions.Construction.infinitesimalSectionsZeroCyclesEquiv_transition I f U hU hcover k (s.val (k + 1)))
    rw [s.property k] at ht
    exact ht.symm

/-- Actual compatible sections give compatible reduced zero-cycles. -/
def infinitesimalSectionsToCompatibleCycles (s : ClopenSections.Construction.infinitesimalGlobalSections I f) :
    CompatibleReducedKernels.Construction.compatibleReducedKernels I ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom :=
  ⟨infinitesimalSectionCycleSequence I f U hU hcover s,
    infinitesimalSectionCycleSequence_compatible I f U hU hcover s,
    fun n => by
      cases n with
      | zero => exact map_zero _
      | succ n => exact (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n (s.val n)).property⟩

/-- Compatible reduced zero-cycles give actual compatible global sections at each level. -/
def compatibleCyclesToInfinitesimalSections
    (x : CompatibleReducedKernels.Construction.compatibleReducedKernels I ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom) :
    ClopenSections.Construction.infinitesimalGlobalSections I f :=
  ⟨fun n => (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n).symm
    ⟨x.val (n + 1), x.property.2 (n + 1)⟩, fun n => by
      apply (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n).injective
      rw [← ZeroCycleTransitions.Construction.infinitesimalSectionsZeroCyclesEquiv_transition, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      exact Subtype.ext (x.property.1 (Nat.le_succ (n + 1)))⟩

theorem infinitesimalSectionsToCompatibleCycles_succ (s : ClopenSections.Construction.infinitesimalGlobalSections I f) (n : ℕ) :
    (infinitesimalSectionsToCompatibleCycles I f U hU hcover s).val (n + 1) =
      (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n (s.val n)).val := rfl

theorem compatibleCyclesToInfinitesimalSections_coordinate
    (x : CompatibleReducedKernels.Construction.compatibleReducedKernels I ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom) (n : ℕ) :
    (compatibleCyclesToInfinitesimalSections I f U hU hcover x).val n =
      (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n).symm
        ⟨x.val (n + 1), x.property.2 (n + 1)⟩ := rfl

/-- The inverse limit of actual infinitesimal global sections is the inverse limit of the
actual reduced native Cech zero-cycles, including the zeroth adic quotient. -/
def infinitesimalGlobalSectionsCompatibleCyclesEquiv :
    ClopenSections.Construction.infinitesimalGlobalSections I f ≃
      CompatibleReducedKernels.Construction.compatibleReducedKernels I ((RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom where
  toFun := infinitesimalSectionsToCompatibleCycles I f U hU hcover
  invFun := compatibleCyclesToInfinitesimalSections I f U hU hcover
  left_inv s := by
    apply Subtype.ext
    funext n
    exact (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n).symm_apply_apply (s.val n)
  right_inv x := by
    apply Subtype.ext
    funext n
    cases n with
    | zero => exact adicZerothQuotient_eq I _ _
    | succ n =>
      rw [infinitesimalSectionsToCompatibleCycles_succ,
        compatibleCyclesToInfinitesimalSections_coordinate]
      exact congrArg Subtype.val
        ((CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n).apply_symm_apply
          ⟨x.val (n + 1), x.property.2 (n + 1)⟩)

theorem infinitesimalGlobalSectionsCompatibleCyclesEquiv_coordinate
    (s : ClopenSections.Construction.infinitesimalGlobalSections I f) (n : ℕ) :
    (infinitesimalGlobalSectionsCompatibleCyclesEquiv I f U hU hcover s).val (n + 1) =
      (CechZeroCycles.Construction.infinitesimalSectionsZeroCyclesEquiv I f U hU hcover n (s.val n)).val := rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CompatibleCycles.Construction
