import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-! # Fppf Cover Detection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfCoverDetection

noncomputable section

/-!
# CartierDuality: detecting Picard-sheaf equalities after an actual fppf point lift
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

namespace Construction.Schemes

variable {S : Scheme.{u}} {T U : Over S} (f : U ⟶ T)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

/-- A native fppf morphism is a singleton cover on the actual site over the base. -/
theorem singleton_fppf_over :
    Sieve.generate (Presieve.singleton f) ∈ (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  change Sieve.generate (Presieve.functorPushforward (Over.forget S) (Presieve.singleton f)) ∈
    Scheme.fppfTopology ((Over.forget S).obj T)
  rw [← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve, Presieve.map_singleton]
  exact Precoverage.generate_mem_toGrothendieck f.left.singleton_mem_fppfPrecoverage

/-- Equality of actual fppf-sheaf sections can be checked after a single fppf cover. -/
theorem fppfSheaf_restriction_injective (F : Sheaf (Scheme.fppfTopology.over S) (Type v)) :
    Function.Injective (F.obj.map f.op) := by
  apply Presieve.isSeparatedFor_singleton.mp
  rw [Presieve.isSeparatedFor_iff_generate]
  exact (F.property.isSheafFor _ (singleton_fppf_over f)).isSeparatedFor

end Construction.Schemes

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B T : Over S} (f : A ⟶ B)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

/-- Every test-scheme point of the quotient lifts along an actual fppf cover. -/
theorem exists_fppf_point_lift (b : T ⟶ B) :
    ∃ (U : Over S) (t : U ⟶ T) (a : U ⟶ A),
      Flat t.left ∧ Surjective t.left ∧ LocallyOfFinitePresentation t.left ∧ a ≫ f = t ≫ b := by
  have sq := (IsPullback.of_hasPullback f b).map (Over.forget S)
  refine ⟨pullback f b, pullback.snd f b, pullback.fst f b, ?_, ?_, ?_, pullback.condition⟩
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq (inferInstanceAs (Flat f.left))
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq (inferInstanceAs (Surjective f.left))
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
      (inferInstanceAs (LocallyOfFinitePresentation f.left))

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfCoverDetection
