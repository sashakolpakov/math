import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.Neighborhoods
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CompatibleClopenSections

/-! # Clopen Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ClopenSections.Construction

noncomputable section

/-!
# Completion: a separated fiber gives an actual compatible infinitesimal idempotent

The homeomorphisms between the actual infinitesimal neighborhoods extend
each initial clopen piece through every thickening. Its characteristic
functions form a canonical compatible idempotent, nontrivial whenever the
initial piece is nontrivial. The formal-functions comparison remains a
separate proof obligation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The actual initial infinitesimal neighborhood is homeomorphic to every later one. -/
def infinitesimalInitialHomeomorph : ∀ n,
    Neighborhoods.Construction.infinitesimalNeighborhood I f 0 ≃ₜ Neighborhoods.Construction.infinitesimalNeighborhood I f n
  | 0 => Homeomorph.refl _
  | n + 1 => (infinitesimalInitialHomeomorph n).trans (Neighborhoods.Construction.infinitesimalTransitionHomeomorph I f n)

variable (U : (Neighborhoods.Construction.infinitesimalNeighborhood I f 0).Opens)

/-- Extension of the initial open subset through the actual infinitesimal homeomorphisms. -/
def infinitesimalClopenExtension (n : ℕ) : (Neighborhoods.Construction.infinitesimalNeighborhood I f n).Opens :=
  ⟨(Construction.infinitesimalInitialHomeomorph I f n).symm ⁻¹' (U : Set _),
    U.isOpen.preimage (Construction.infinitesimalInitialHomeomorph I f n).symm.continuous⟩

theorem infinitesimalClopenExtension_isClosed
    (hU : IsClosed (U : Set (Neighborhoods.Construction.infinitesimalNeighborhood I f 0))) (n : ℕ) :
    IsClosed (infinitesimalClopenExtension I f U n : Set (Neighborhoods.Construction.infinitesimalNeighborhood I f n)) :=
  hU.preimage (Construction.infinitesimalInitialHomeomorph I f n).symm.continuous

/-- The extended clopen pieces restrict to each other along the actual transition maps. -/
theorem infinitesimalClopenExtension_compatible (n : ℕ) :
    Neighborhoods.Construction.infinitesimalTransition I f n ⁻¹ᵁ infinitesimalClopenExtension I f U (n + 1) =
      infinitesimalClopenExtension I f U n := by
  ext x
  change (Construction.infinitesimalInitialHomeomorph I f n).symm
      ((Neighborhoods.Construction.infinitesimalTransitionHomeomorph I f n).symm
        ((Neighborhoods.Construction.infinitesimalTransitionHomeomorph I f n) x)) ∈ U ↔
    (Construction.infinitesimalInitialHomeomorph I f n).symm x ∈ U
  rw [Homeomorph.symm_apply_apply]

/-- The actual ring of compatible global functions on these infinitesimal neighborhoods. -/
abbrev infinitesimalGlobalSections :=
  CompatibleClopenSections.Construction.compatibleGlobalSections (Neighborhoods.Construction.infinitesimalNeighborhood I f) (Neighborhoods.Construction.infinitesimalTransition I f)

/-- The canonical compatible infinitesimal idempotent attached to the initial clopen piece. -/
def infinitesimalClopenIndicator (hU : IsClosed (U : Set (Neighborhoods.Construction.infinitesimalNeighborhood I f 0))) :
    infinitesimalGlobalSections I f :=
  CompatibleClopenSections.Construction.compatibleClopenIndicator _ _ (infinitesimalClopenExtension I f U)
    (infinitesimalClopenExtension_isClosed I f U hU)
    (infinitesimalClopenExtension_compatible I f U)

/-- A nontrivial initial clopen piece produces a nontrivial idempotent in the actual compatible
infinitesimal global sections. -/
theorem infinitesimalClopenIndicator_nontrivial
    (hU : IsClosed (U : Set (Neighborhoods.Construction.infinitesimalNeighborhood I f 0)))
    (h₀ : U ≠ ⊥) (h₁ : U ≠ ⊤) :
    IsIdempotentElem (infinitesimalClopenIndicator I f U hU) ∧
      infinitesimalClopenIndicator I f U hU ≠ 0 ∧
      infinitesimalClopenIndicator I f U hU ≠ 1 := by
  refine ⟨CompatibleClopenSections.Construction.compatibleClopenIndicator_isIdempotent _ _ _ _ _, ?_, ?_⟩
  · intro h
    have he := congrArg (fun s : infinitesimalGlobalSections I f => s.val 0) h
    change ClopenIdempotents.Construction.clopenIndicator U hU = 0 at he
    exact h₀ ((ClopenIdempotents.Construction.clopenIndicator_eq_zero_iff U hU).mp he)
  · intro h
    have he := congrArg (fun s : infinitesimalGlobalSections I f => s.val 0) h
    change ClopenIdempotents.Construction.clopenIndicator U hU = 1 at he
    exact h₁ ((ClopenIdempotents.Construction.clopenIndicator_eq_one_iff U hU).mp he)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.ClopenSections.Construction
