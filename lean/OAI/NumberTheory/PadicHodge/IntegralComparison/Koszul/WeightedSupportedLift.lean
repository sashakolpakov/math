import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CanonicalSupportedLift

/-! # Weighted Supported Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.WeightedSupportedLift

noncomputable section

/-! Evaluation of finite quotient coefficients reduces to weighted
point quotients. Their supported fraction is normalized by the same
literal scalar, independently of every projective-resolution lift. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionSupportedUniqueness

theorem dual_map_smul (R : Type u) [CommRing R]
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (a : K ⟶ L) (r : R) :
    DualComplexHomology.map R (r • a) = r • DualComplexHomology.map R a := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  exact φ.map_smul r _

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  (V : ProjectiveResolution (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.normalIdeal R s)))
  (Q : ProjectiveResolution (ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t)))
  (r : R) (a : V.complex ⟶ Q.complex)
  (ha : a ≫ Q.π = V.π ≫ (ChainComplex.single₀ (ModuleCat R)).map (r • KoszulPartial.Resolution.quotient R s t))

def ambient_homotopy : Homotopy (CanonicalSupportedLift.ambientMap R P s t hs V Q a)
    ((r • ResolutionSupportedUniqueness.cochainMap R P U s t ht hst Q) ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s)) := by
  have hb : (r • KoszulPartial.Resolution.inclusion R s t) ≫ (KoszulPartial.Resolution.pointResolution R s t hst).π =
      (KoszulPartial.Resolution.normalResolution R s hs).π ≫
        (ChainComplex.single₀ (ModuleCat R)).map (r • KoszulPartial.Resolution.quotient R s t) := by
    apply (ChainComplex.toSingle₀Equiv _ _).injective
    apply Subtype.ext
    change ((r • KoszulPartial.Resolution.inclusion R s t) ≫ (KoszulPartial.Resolution.pointResolution R s t hst).π).f 0 =
      ((KoszulPartial.Resolution.normalResolution R s hs).π ≫
        (ChainComplex.single₀ (ModuleCat R)).map (r • KoszulPartial.Resolution.quotient R s t)).f 0
    have h := congrArg (fun z => z.f 0) (KoszulPartial.Resolution.augmentation R s t hs hst)
    simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at h ⊢
    change (r • (KoszulPartial.Resolution.inclusion R s t).f 0) ≫ (KoszulPartial.Resolution.pointResolution R s t hst).π.f 0 =
      (KoszulPartial.Resolution.normalResolution R s hs).π.f 0 ≫ (r • KoszulPartial.Resolution.quotient R s t)
    rw [Linear.smul_comp, Linear.comp_smul, h]
  let h := IntegralComparison.ProjectiveResolution.HomotopyNaturality.naturality
    (ExactModuleDualFunctor.functor R) (r • KoszulPartial.Resolution.quotient R s t)
    V (KoszulPartial.Resolution.normalResolution R s hs) Q (KoszulPartial.Resolution.pointResolution R s t hst)
    a (r • KoszulPartial.Resolution.inclusion R s t) ha hb
  have he : ((ResolutionSupportedUniqueness.equivalence R s t hst Q).hom ≫
      DualComplexHomology.map R (r • KoszulPartial.Resolution.inclusion R s t)) ≫
        KoszulPartial.CanonicalMap.scalarsMap R P s =
      (r • ResolutionSupportedUniqueness.cochainMap R P U s t ht hst Q) ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s) := by
    rw [dual_map_smul, Linear.comp_smul, Linear.smul_comp, Linear.smul_comp]
    apply congrArg (fun z => r • z)
    rw [ResolutionSupportedUniqueness.cochainMap, Category.assoc]
    change _ = _ ≫ KoszulPartial.Forget.ambientMap R P U s t ht
    rw [KoszulPartial.CanonicalMap.forget_factorization]
  exact (Homotopy.ofEq (Category.assoc _ _ _).symm).trans
    ((h.compRight (KoszulPartial.CanonicalMap.scalarsMap R P s)).trans (Homotopy.ofEq he))

def homotopy (f : DualComplexHomology.complex R Q.complex ⟶
    (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (hf : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))
      (CanonicalSupportedLift.ambientMap R P s t hs V Q a)) :
    Homotopy f (r • ResolutionSupportedUniqueness.cochainMap R P U s t ht hst Q) :=
  ResolutionSupportedUniqueness.homotopy R P U s t ht hst Q f _
    (hf.trans (ambient_homotopy R P U s t ht hs hst V Q r a ha))

include ha in
theorem homology (f : DualComplexHomology.complex R Q.complex ⟶
    (KoszulPartial.Components.target R P U s).total (.up ℕ))
    (hf : Homotopy (f ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s))
      (CanonicalSupportedLift.ambientMap R P s t hs V Q a)) (n : ℕ) :
    homologyMap f n = r • KoszulPartial.SupportedMap.map R P U s t ht hst Q n := by
  rw [← ResolutionSupportedUniqueness.cochainMap_homology, ← Resolution.CohomologyMaps.homologyMap_smul R]
  exact (homotopy R P U s t ht hs hst V Q r a ha f hf).homologyMap_eq n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.WeightedSupportedLift
