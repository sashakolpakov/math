import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.TotalTop
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

/-! # Partial Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.PartialClass

noncomputable section

/-! Arbitrary top dual-Koszul coefficients give the actual supported
partial-fraction cohomology class. No choice of a unit generator is made. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

def sourceCycle (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m)))) :
    IntegralComparison.Module.CochainClasses.cycles (Components.source R s t) (c + m) :=
  ⟨φ, by
    apply LinearMap.ext
    intro x
    have hx := Exterior.PowerVanishing.eq_zero
      (TopResidue.basis R (c := c) (m := m)) (Nat.lt_succ_self (c + m)) x
    rw [hx, map_zero, map_zero]⟩

def sourceClass (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m)))) :
    (Components.source R s t).homology (c + m) :=
  IntegralComparison.Module.CochainClasses.classMap _ _ (sourceCycle R s t φ)

def supportedCycle (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m)))) :
    IntegralComparison.Module.CochainClasses.cycles ((Components.target R P U s).total (.up ℕ)) (c + m) :=
  IntegralComparison.Module.CochainClassNaturality.cycleMap (Total.map R P U s t ht) _ (sourceCycle R s t φ)

def supportedClass (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m)))) :
    ((Components.target R P U s).total (.up ℕ)).homology (c + m) :=
  IntegralComparison.Module.CochainClasses.classMap _ _ (supportedCycle R P U s t ht φ)

theorem supportedClass_eq (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m)))) :
    supportedClass R P U s t ht φ =
      homologyMap (Total.map R P U s t ht) (c + m) (sourceClass R s t φ) :=
  IntegralComparison.Module.CochainClassNaturality.naturality_apply _ _ _

theorem supportedCycle_val (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m)))) :
    (supportedCycle R P U s t ht φ).val =
      (Components.target R P U s).ιTotal (.up ℕ) c m (c + m) rfl
        (Components.component R P U t ht (c + m) c m rfl φ) := by
  change (Total.map R P U s t ht).f (c + m)
    (show (Components.source R s t).X (c + m) from φ) = _
  exact ConcreteCategory.congr_hom (TotalTop.top_map R P U s t ht)
    (show (Components.source R s t).X (c + m) from φ)

theorem coefficient (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m))))
    (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    (Components.coordinateAt R P U t ht (c + m) c m rfl a φ)
      (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))) =
    Fractions.reciprocal R P U t ht a * algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U m).obj a)))
      (φ (TopExteriorCoordinates.generator
        (TopResidue.basis R (c := c) (m := m)))) := by
  change Fractions.reciprocal R P U t ht a * algebraMap R _
    (φ (Differential.insertionAt R c m (c + m) rfl a
      (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))))) = _
  have he := TopResidue.insertion_top R (c := c) a
  change Differential.insertionAt R c m (c + m) rfl a
    (TopExteriorCoordinates.generator (Pi.basisFun R (Fin c))) = _ at he
  rw [he]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.PartialClass
