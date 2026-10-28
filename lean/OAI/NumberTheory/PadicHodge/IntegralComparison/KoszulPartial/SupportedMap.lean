import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CanonicalMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.PartialClass

/-! # Supported Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.SupportedMap

noncomputable section

/-! The supported fraction map for an arbitrary projective resolution
of the point quotient, normalized by its canonical quotient Ext map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  (Q : ProjectiveResolution (ModuleCat.of R (R ⧸ Resolution.pointIdeal R s t)))

def map (n : ℕ) : (DualComplexHomology.complex R Q.complex).homology n ⟶
    ((Components.target R P U s).total (.up ℕ)).homology n :=
  (IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
    Q (Resolution.pointResolution R s t hst) n).hom ≫
      homologyMap (Total.map R P U s t ht) n

theorem canonical_transport (n : ℕ) :
    (IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
      Q (Resolution.pointResolution R s t hst) n).hom ≫
        Resolution.CohomologyMaps.map (ExactModuleDualFunctor.functor R)
          (Resolution.normalResolution R s hs) (Resolution.pointResolution R s t hst) (Resolution.quotient R s t) n =
    Resolution.CohomologyMaps.map (ExactModuleDualFunctor.functor R)
      (Resolution.normalResolution R s hs) Q (Resolution.quotient R s t) n := by
  exact (Resolution.CohomologyMaps.map_comp (ExactModuleDualFunctor.functor R)
    (Resolution.normalResolution R s hs) (Resolution.pointResolution R s t hst) Q (Resolution.quotient R s t) (𝟙 _) n).symm

theorem forget (n : ℕ) :
    map R P U s t ht hst Q n ≫
      homologyMap (AugmentedOrdered.CechForget.forgetSupport U (Components.coefficient R P s)) n =
    Resolution.CohomologyMaps.map (ExactModuleDualFunctor.functor R)
      (Resolution.normalResolution R s hs) Q (Resolution.quotient R s t) n ≫
        homologyMap (CanonicalMap.scalarsMap R P s) n := by
  rw [map, Category.assoc, ← homologyMap_comp]
  change _ ≫ homologyMap (Forget.ambientMap R P U s t ht) n = _
  rw [CanonicalMap.canonical_map R P U s t ht hs hst n,
    ← Category.assoc, canonical_transport R s t hs hst Q n]

theorem class_eq (z : (DualComplexHomology.complex R Q.complex).homology (c + m))
    (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m))))
    (hφ : (IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
      Q (Resolution.pointResolution R s t hst) (c + m)).hom z = PartialClass.sourceClass R s t φ) :
    map R P U s t ht hst Q (c + m) z = PartialClass.supportedClass R P U s t ht φ := by
  change homologyMap (Total.map R P U s t ht) (c + m)
    ((IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
      Q (Resolution.pointResolution R s t hst) (c + m)).hom z) = _
  rw [hφ, PartialClass.supportedClass_eq]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.SupportedMap
