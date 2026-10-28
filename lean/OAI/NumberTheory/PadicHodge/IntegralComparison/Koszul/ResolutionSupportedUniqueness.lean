import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedUniqueness
import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.SupportedMap

/-! # Resolution Supported Uniqueness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionSupportedUniqueness

noncomputable section

/-! The canonical supported point map for any genuine projective
resolution, with uniqueness and representatives for every point class. -/
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
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  (Q : ProjectiveResolution (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t)))

abbrev equivalence := IntegralComparison.ProjectiveResolution.Hom.Comparison.homotopyEquiv
  (ExactModuleDualFunctor.functor R) Q (KoszulPartial.Resolution.pointResolution R s t hst)

def cochainMap : DualComplexHomology.complex R Q.complex ⟶ (KoszulPartial.Components.target R P U s).total (.up ℕ) :=
  (equivalence R s t hst Q).hom ≫ KoszulPartial.Total.map R P U s t ht

theorem cochainMap_homology (n : ℕ) :
    homologyMap (cochainMap R P U s t ht hst Q) n =
      KoszulPartial.SupportedMap.map R P U s t ht hst Q n := by
  rw [cochainMap, homologyMap_comp]
  rfl

def homotopy (f g : DualComplexHomology.complex R Q.complex ⟶
    (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (h : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))
      (g ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))) : Homotopy f g := by
  let e := equivalence R s t hst Q
  let h' := SupportedUniqueness.homotopy R P U s t ht (e.inv ≫ f) (e.inv ≫ g)
    ((Homotopy.ofEq (Category.assoc _ _ _)).trans
      ((h.compLeft e.inv).trans (Homotopy.ofEq (Category.assoc _ _ _).symm)))
  exact (e.homotopyHomInvId.compRightId f).symm.trans
    ((Homotopy.ofEq (Category.assoc _ _ _)).trans
      ((h'.compLeft e.hom).trans
        ((Homotopy.ofEq (Category.assoc _ _ _).symm).trans
          (e.homotopyHomInvId.compRightId g))))

theorem homology_eq (f : DualComplexHomology.complex R Q.complex ⟶
    (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (h : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))
      (cochainMap R P U s t ht hst Q ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))) (n : ℕ) :
    homologyMap f n = KoszulPartial.SupportedMap.map R P U s t ht hst Q n := by
  rw [← cochainMap_homology]
  exact (homotopy R P U s t ht hst Q f _ h).homologyMap_eq n

theorem sourceClass_surjective : Function.Surjective (KoszulPartial.PartialClass.sourceClass R s t) := by
  intro z
  obtain ⟨x, hx⟩ := IntegralComparison.Module.CochainClasses.classMap_surjective (KoszulPartial.Components.source R s t) (c + m) z
  refine ⟨x.val, ?_⟩
  exact (congrArg (IntegralComparison.Module.CochainClasses.classMap (KoszulPartial.Components.source R s t) (c + m))
    (show KoszulPartial.PartialClass.sourceCycle R s t x.val = x from Subtype.ext rfl)).trans hx

theorem represents (z : (DualComplexHomology.complex R Q.complex).homology (c + m)) :
    ∃ φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m))),
      (IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
        Q (KoszulPartial.Resolution.pointResolution R s t hst) (c + m)).hom z = KoszulPartial.PartialClass.sourceClass R s t φ ∧
      KoszulPartial.SupportedMap.map R P U s t ht hst Q (c + m) z =
        KoszulPartial.PartialClass.supportedClass R P U s t ht φ := by
  obtain ⟨φ, hφ⟩ := sourceClass_surjective R s t
    ((IntegralComparison.ProjectiveResolution.Hom.Comparison.homologyIso (ExactModuleDualFunctor.functor R)
      Q (KoszulPartial.Resolution.pointResolution R s t hst) (c + m)).hom z)
  exact ⟨φ, hφ.symm, KoszulPartial.SupportedMap.class_eq R P U s t ht hst Q z φ hφ.symm⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionSupportedUniqueness
