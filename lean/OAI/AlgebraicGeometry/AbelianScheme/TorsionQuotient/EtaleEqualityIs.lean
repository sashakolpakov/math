import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FiniteEtaleLift
import Mathlib.Topology.Clopen

/-! # Etale Equality Is -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleEqualityIs.EtaleEquality

/-!
# TorsionQuotient: clopen equality loci in finite etale parameter schemes
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {P H : Over S}
variable [IsFinite P.hom] [Etale P.hom] [IsFinite H.hom] [Etale H.hom]

theorem range_isClopen (f g : P ⟶ H) : IsClopen (Set.range (equalizer.ι f g).left) := by
  obtain ⟨ho, hc⟩ := FiniteEtaleLift.FiniteEtaleLimits.equalizer_open_closed f g
  let : IsOpenImmersion (equalizer.ι f g).left := ho
  let : IsClosedImmersion (equalizer.ι f g).left := hc
  exact ⟨(equalizer.ι f g).left.isClosedEmbedding.isClosed_range,
    (equalizer.ι f g).left.isOpenEmbedding.isOpen_range⟩

/-- Equality after an arbitrary base change is exactly factorization
through the open equality locus, including for nonreduced test schemes. -/
theorem equalizes_iff_range_subset (f g : P ⟶ H) {T : Over S} (a : T ⟶ P) :
    a ≫ f = a ≫ g ↔ Set.range a.left ⊆ Set.range (equalizer.ι f g).left := by
  let : IsOpenImmersion (equalizer.ι f g).left :=
    (FiniteEtaleLift.FiniteEtaleLimits.equalizer_open_closed f g).1
  constructor
  · intro ha
    rintro _ ⟨x, rfl⟩
    refine ⟨(equalizer.lift a ha).left x, ?_⟩
    change ((equalizer.lift a ha).left ≫ (equalizer.ι f g).left) x = a.left x
    rw [← Over.comp_left, equalizer.lift_ι]
  · intro ha
    let l := IsOpenImmersion.lift (equalizer.ι f g).left a.left ha
    have hl : l ≫ (equalizer.ι f g).left = a.left := IsOpenImmersion.lift_fac _ _ ha
    apply Over.OverMorphism.ext
    change a.left ≫ f.left = a.left ≫ g.left
    rw [← hl, Category.assoc, Category.assoc]
    exact congrArg (fun z => l ≫ z.left) (equalizer.condition f g)

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleEqualityIs.EtaleEquality
