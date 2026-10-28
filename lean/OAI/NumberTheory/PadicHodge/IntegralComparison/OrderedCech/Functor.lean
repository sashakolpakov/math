import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Projection

/-! # Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor.Projection

noncomputable section

/-! The original ordered nonempty Čech complex as an additive functor
of its coefficient presheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {D : Type v} [Category D] [Preadditive D] [HasProducts.{u} D]

def complexMap {P Q : Cᵒᵖ ⥤ D} (f : P ⟶ Q) : Projection.complex U P ⟶ Projection.complex U Q :=
  CochainComplex.ofHom (fun n => AugmentedOrdered.CechFunctor.objectMap U f (n + 1))
    (fun n => by
      simpa only [Projection.complex, CochainComplex.of_d, Projection.differential] using
        AugmentedOrdered.CechFunctor.objectMap_differential U f (n + 1))

def functor : (Cᵒᵖ ⥤ D) ⥤ CochainComplex D ℕ where
  obj := Projection.complex U
  map := complexMap U
  map_id P := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrArg (fun f => f.f (n + 1)) (AugmentedOrdered.CechFunctor.functor U |>.map_id P)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrArg (fun f => f.f (n + 1)) (AugmentedOrdered.CechFunctor.functor U |>.map_comp f g)

instance additive : (functor U (D := D)).Additive where
  map_add {P Q} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact congrArg (fun h => h.f (n + 1))
      ((AugmentedOrdered.CechFunctor.functor U).map_add (f := f) (g := g))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Functor.Projection
