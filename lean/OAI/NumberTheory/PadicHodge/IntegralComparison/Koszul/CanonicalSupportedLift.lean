import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionSupportedUniqueness
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.HomotopyNaturality

/-! # Canonical Supported Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CanonicalSupportedLift

noncomputable section

/-! A supported lift of an actual augmentation-preserving point
quotient map agrees with the canonical mixed partial fraction map.
Both projective resolutions may be arbitrary. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionSupportedUniqueness
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  (V : ProjectiveResolution (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.normalIdeal R s)))
  (Q : ProjectiveResolution (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t)))
  (a : V.complex ⟶ Q.complex)
  (ha : a ≫ Q.π = V.π ≫ (ChainComplex.single₀ (ModuleCat R)).map (KoszulPartial.Resolution.quotient R s t))

def ambientMap : DualComplexHomology.complex R Q.complex ⟶ AugmentedOrdered.CechForget.ambientComplex (KoszulPartial.Components.coefficient R P s) :=
  DualComplexHomology.map R a ≫
    (IntegralComparison.ProjectiveResolution.Hom.Comparison.homotopyEquiv (ExactModuleDualFunctor.functor R)
      V (KoszulPartial.Resolution.normalResolution R s hs)).hom ≫ KoszulPartial.CanonicalMap.scalarsMap R P s

def ambient_homotopy : Homotopy (ambientMap R P s t hs V Q a)
    (ResolutionSupportedUniqueness.cochainMap R P U s t ht hst Q ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s)) := by
  let h := IntegralComparison.ProjectiveResolution.HomotopyNaturality.naturality
    (ExactModuleDualFunctor.functor R) (KoszulPartial.Resolution.quotient R s t)
    V (KoszulPartial.Resolution.normalResolution R s hs) Q (KoszulPartial.Resolution.pointResolution R s t hst)
    a (KoszulPartial.Resolution.inclusion R s t) ha (KoszulPartial.Resolution.augmentation R s t hs hst)
  have he : ResolutionSupportedUniqueness.cochainMap R P U s t ht hst Q ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s) =
      (ResolutionSupportedUniqueness.equivalence R s t hst Q).hom ≫
        DualComplexHomology.map R (KoszulPartial.Resolution.inclusion R s t) ≫
          KoszulPartial.CanonicalMap.scalarsMap R P s := by
    rw [ResolutionSupportedUniqueness.cochainMap, Category.assoc]
    change _ ≫ KoszulPartial.Forget.ambientMap R P U s t ht = _
    rw [KoszulPartial.CanonicalMap.forget_factorization]
  exact (Homotopy.ofEq (Category.assoc _ _ _).symm).trans
    ((h.compRight (KoszulPartial.CanonicalMap.scalarsMap R P s)).trans
      (Homotopy.ofEq ((Category.assoc _ _ _).trans he.symm)))

def homotopy (f : DualComplexHomology.complex R Q.complex ⟶
    (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (hf : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s)) (ambientMap R P s t hs V Q a)) :
    Homotopy f (ResolutionSupportedUniqueness.cochainMap R P U s t ht hst Q) :=
  ResolutionSupportedUniqueness.homotopy R P U s t ht hst Q f _
    (hf.trans (ambient_homotopy R P U s t ht hs hst V Q a ha))

include ha in
theorem homology (f : DualComplexHomology.complex R Q.complex ⟶
    (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (hf : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s)) (ambientMap R P s t hs V Q a))
    (n : ℕ) : homologyMap f n = KoszulPartial.SupportedMap.map R P U s t ht hst Q n := by
  rw [← ResolutionSupportedUniqueness.cochainMap_homology]
  exact (homotopy R P U s t ht hs hst V Q a ha f hf).homologyMap_eq n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CanonicalSupportedLift
