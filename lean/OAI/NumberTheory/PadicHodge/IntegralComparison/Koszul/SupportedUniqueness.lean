import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.SupportedUniqueness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.PuncturedHomRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.PartialClass

/-! # Supported Uniqueness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedUniqueness

noncomputable section

/-! The mixed partial-fraction map is the unique supported lift, up to
actual homotopy, of its canonical ambient dual-Koszul map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

def homotopy (f g : KoszulPartial.Components.source R s t ⟶ (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (h : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))
      (g ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))) : Homotopy f g :=
  AugmentedCech.SupportedUniqueness.homotopy U (KoszulPartial.Components.coefficient R P s) (KoszulPartial.Components.source R s t)
    (PuncturedHomRows.positive R P U s t ht) f g h

def to_partial (f : KoszulPartial.Components.source R s t ⟶ (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (h : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))
      (KoszulPartial.Total.map R P U s t ht ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))) :
    Homotopy f (KoszulPartial.Total.map R P U s t ht) :=
  homotopy R P U s t ht f _ h

theorem homology_eq (f : KoszulPartial.Components.source R s t ⟶ (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (h : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))
      (KoszulPartial.Total.map R P U s t ht ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s)))
    (n : ℕ) : homologyMap f n = homologyMap (KoszulPartial.Total.map R P U s t ht) n :=
  (to_partial R P U s t ht f h).homologyMap_eq n

theorem class_eq (f : KoszulPartial.Components.source R s t ⟶ (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (h : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))
      (KoszulPartial.Total.map R P U s t ht ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s)))
    (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    homologyMap f (c + m) (KoszulPartial.PartialClass.sourceClass R s t φ) =
      KoszulPartial.PartialClass.supportedClass R P U s t ht φ := by
  rw [homology_eq R P U s t ht f h, KoszulPartial.PartialClass.supportedClass_eq]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedUniqueness
