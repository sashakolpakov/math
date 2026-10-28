import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateSupportedLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality

/-! # Supported Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedLift

noncomputable section

/-! The explicit supported lift for the full point sequence `(s,t)`.
Its support-forgetting identity is preserved by every actual coefficient
cochain map, including the oriented purity map to the surviving point. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable (R : Type u) [CommRing R] {c m : ℕ}

def parameterInclusion : (Fin m → R) →ₗ[R] (Fin (c + m) → R) where
  toFun v := Fin.append 0 v
  map_add' v w := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' r v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

variable (s : Fin c → R) (t : Fin m → R)

theorem equation_parameterInclusion :
    (Koszul.GeneratorMatrix.equation R (Fin.append s t)).comp
      (parameterInclusion R) = Koszul.GeneratorMatrix.equation R t := by
  apply LinearMap.ext
  intro x
  simp [parameterInclusion, Koszul.GeneratorMatrix.equation_apply, Fin.sum_univ_add]

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R) (U : ULift.{u} (Fin m) → C)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

abbrev lift := Koszul.DuplicateSupportedLift.lift R (Fin.append s t) t
  (parameterInclusion R) (equation_parameterInclusion R s t) P U ht

@[reassoc]
theorem lift_forget : lift R s t P U ht ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P (Fin.append s t)) =
    KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t) :=
  Koszul.DuplicateSupportedLift.lift_forget R (Fin.append s t) t
    (parameterInclusion R) (equation_parameterInclusion R s t) P U ht

variable {L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (b : KoszulPartial.Components.coefficient R P (Fin.append s t) ⟶ L)

def map : DualComplexHomology.complex R
    (Koszul.OrientedTopCohomology.koszul R (Fin.append s t)) ⟶
      (AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ) :=
  lift R s t P U ht ≫ AugmentedOrdered.CechForgetNaturality.map U b

@[reassoc]
theorem map_forget : map R s t P U ht b ≫ AugmentedOrdered.CechForget.forgetSupport U L =
    KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t) ≫
      AugmentedOrdered.CechForgetNaturality.ambientMap b := by
  dsimp only [map]
  rw [Category.assoc, AugmentedOrdered.CechForgetNaturality.comparison,
    ← Category.assoc, lift_forget]

theorem homology_forget (q : ℕ) : homologyMap (map R s t P U ht b) q ≫
    homologyMap (AugmentedOrdered.CechForget.forgetSupport U L) q =
      homologyMap (KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t)) q ≫
        homologyMap (AugmentedOrdered.CechForgetNaturality.ambientMap b) q := by
  simpa only [homologyMap_comp] using
    congrArg (fun f => homologyMap f q) (map_forget R s t P U ht b)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedLift
