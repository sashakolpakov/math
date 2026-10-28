import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Factorial
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Stalk Factorial -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.StalkFactorial.SmoothStalkFactorial

noncomputable section

/-! Factoriality of smooth geometrically integral stalks over arbitrary fields, by faithfully flat descent from the algebraic closure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem of_flat_surjective {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    (g : Y ⟶ X) [Flat g] [Surjective g]
    (hY : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  obtain ⟨y, rfl⟩ := g.surjective x
  let : Algebra (X.presheaf.stalk (g y)) (Y.presheaf.stalk y) :=
    (g.stalkMap y).hom.toAlgebra
  let : Module.FaithfullyFlat (X.presheaf.stalk (g y)) (Y.presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap g y) (g.toLRSHom.prop y)
  let : UniqueFactorizationMonoid (Y.presheaf.stalk y) := hY y
  exact OAI.AlgebraicGeometry.Quotients.FiniteDescent.Factorial.Construction.FactorialDescent.of_faithfullyFlat (S := Y.presheaf.stalk y)

theorem stalk {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] [GeometricallyIntegral f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let : Surjective g := ⟨fun z => ⟨IsLocalRing.closedPoint (AlgebraicClosure K),
    Subsingleton.elim _ z⟩⟩
  exact of_flat_surjective (pullback.fst f g)
    (OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk (pullback.snd f g)) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.StalkFactorial.SmoothStalkFactorial
