import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Test Monomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TestMonomorphism

noncomputable section

/-! A finite-type comparison from a locally Noetherian parameter is a
monomorphism once equality is detected on locally Noetherian tests.
The proof tests the two projections of the actual self-fiber product,
then uses its universal property for arbitrary test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem mono_of_locallyNoetherian_tests
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T] (a b : T ⟶ X),
      a ≫ f = b ≫ f → a = b) : Mono f := by
  let : IsLocallyNoetherian (pullback f f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f)
  have hp : pullback.fst f f = pullback.snd f f :=
    h (pullback f f) (pullback.fst f f) (pullback.snd f f) pullback.condition
  constructor
  intro T a b hab
  let l : T ⟶ pullback f f := pullback.lift a b hab
  exact (pullback.lift_fst a b hab).symm.trans
    ((congrArg (fun p => l ≫ p) hp).trans (pullback.lift_snd a b hab))

theorem over_mono_of_locallyNoetherian_tests
    {S : Scheme.{u}} {X Y : Over S} [IsLocallyNoetherian X.left]
    (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (h : ∀ (T : Over S) [IsLocallyNoetherian T.left] (a b : T ⟶ X),
      a ≫ f = b ≫ f → a = b) : Mono f := by
  let : Mono f.left := mono_of_locallyNoetherian_tests f.left (by
    intro T _ a b hab
    let U : Over S := Over.mk (a ≫ X.hom)
    let : IsLocallyNoetherian U.left := inferInstanceAs (IsLocallyNoetherian T)
    let a' : U ⟶ X := Over.homMk a rfl
    have hb : b ≫ X.hom = a ≫ X.hom := by
      have hc := congrArg (fun p => p ≫ Y.hom) hab
      simpa only [Category.assoc, f.w] using hc.symm
    let b' : U ⟶ X := Over.homMk b hb
    exact congrArg Over.Hom.left (h U a' b' (Over.OverMorphism.ext hab)))
  exact Over.mono_of_mono_left f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TestMonomorphism
