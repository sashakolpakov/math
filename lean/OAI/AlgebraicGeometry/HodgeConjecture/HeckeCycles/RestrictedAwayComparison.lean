import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedAwaySame

/-! # Restricted Away Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedAwayComparison.CM

noncomputable section

/-! Compare the identity-component model of the away group with the
restricted product indexed by the other places. -/

open scoped Classical RestrictedProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedAwaySame.Approximation

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct.CM

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
  (K : ∀ i, Subgroup (G i)) (v : I)

def forget : RestrictedPlaceProduct.CM.away K v →* CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway K v :=
  (CMExtraction.RestrictedAwaySame.Approximation.restrictedForgetPlace K v).comp (RestrictedPlaceProduct.CM.away K v).subtype

theorem forget_apply (g : RestrictedPlaceProduct.CM.away K v) (w : {w : I // w ≠ v}) :
    forget K v g w = g.val w.val := rfl

theorem forget_remove (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) :
    forget K v (RestrictedPlaceProduct.CM.awayHom K v g) = CMExtraction.RestrictedAwaySame.Approximation.restrictedForgetPlace K v g := by
  apply RestrictedProduct.ext
  intro w
  exact RestrictedPlaceProduct.CM.remove_other K v g w.property

theorem forget_injective : Function.Injective (forget K v) := by
  intro g h he
  apply Subtype.ext
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst w
    exact g.property.trans h.property.symm
  · exact congrArg (fun z : CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway K v => z ⟨w, hw⟩) he

variable [∀ i, TopologicalSpace (G i)]

theorem forget_continuous : Continuous (forget K v) :=
  (CMExtraction.RestrictedAwaySame.Approximation.restrictedForgetPlace_continuous K v).comp continuous_subtype_val

instance away_topologicalGroup [∀ i, IsTopologicalGroup (G i)]
    [Fact (∀ i, IsOpen (K i : Set (G i)))] : IsTopologicalGroup (CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway K v) := by
  let : Fact (∀ w : {w : I // w ≠ v}, IsOpen (K w.val : Set (G w.val))) :=
    ⟨fun w => Fact.out (p := ∀ i, IsOpen (K i : Set (G i))) w.val⟩
  infer_instance

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedAwayComparison.CM
