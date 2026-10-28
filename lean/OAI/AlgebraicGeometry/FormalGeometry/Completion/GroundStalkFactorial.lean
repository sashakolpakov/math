import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Factorial
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.MapFaithful
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Ground Stalk Factorial -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundStalkFactorial

noncomputable section

/-! Local factoriality over the ground field descends from the actual
geometric fiber through its faithfully flat local stalk maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

theorem ground_stalk_uniqueFactorization
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [GeometricallyIntegral f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  let B := pullback f (Geometric.Frobenius.Construction.algebraicClosureBase K)
  let p : B ⟶ X := pullback.fst f (Geometric.Frobenius.Construction.algebraicClosureBase K)
  let g : B ⟶ Spec (CommRingCat.of (AlgebraicClosure K)) := pullback.snd f (Geometric.Frobenius.Construction.algebraicClosureBase K)
  have : Flat (Geometric.Frobenius.Construction.algebraicClosureBase K) := (Geometric.MapFaithful.Construction.algebraicClosureBase_flat_surjective K).1
  have : Surjective (Geometric.Frobenius.Construction.algebraicClosureBase K) := (Geometric.MapFaithful.Construction.algebraicClosureBase_flat_surjective K).2
  have : Flat p := inferInstanceAs (Flat (pullback.fst f (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : Surjective p := inferInstanceAs (Surjective (pullback.fst f (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : Smooth g := inferInstanceAs (Smooth (pullback.snd f (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : GeometricallyIntegral g :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd f (Geometric.Frobenius.Construction.algebraicClosureBase K)))
  have : IsIntegral B := GeometricallyIntegral.isIntegral_of_subsingleton g
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨y, rfl⟩ := (inferInstance : Surjective p).surj x
  let R := X.presheaf.stalk (p y)
  let S := B.presheaf.stalk y
  let : Algebra R S := (p.stalkMap y).hom.toAlgebra
  have : Module.Flat R S := Flat.stalkMap p y
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (p.stalkMap y).hom)
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : UniqueFactorizationMonoid S := Quotients.FiniteDescent.SmoothStalk.Construction.SmoothStalkFactorial.stalk g y
  exact Quotients.FiniteDescent.Factorial.Construction.FactorialDescent.of_faithfullyFlat (R := R) (S := S)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundStalkFactorial
