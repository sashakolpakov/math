import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert

/-! # Restricted Fill Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedFillComparison.CM

noncomputable section

/-! Removing a local factor is exactly insertion of the identity into
the complementary restricted product. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert.Approximation

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
  (K : ∀ i, Subgroup (G i)) (v : I)

def fill : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K →* RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K :=
  (RestrictedPlaceProduct.CM.away K v).subtype.comp (RestrictedPlaceProduct.CM.awayHom K v)

theorem same (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) : fill K v g v = 1 :=
  RestrictedPlaceProduct.CM.remove_same K v g

theorem other (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) {w : I} (hw : w ≠ v) : fill K v g w = g w :=
  RestrictedPlaceProduct.CM.remove_other K v g hw

theorem inserted (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) :
    fill K v g = CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace K v (CMExtraction.RestrictedAwaySame.Approximation.restrictedForgetPlace K v g) := by
  apply RestrictedProduct.ext
  intro w
  by_cases hw : w = v
  · subst w
    rw [same, CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace_same]
  · rw [other K v g hw, CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace_other K v _ w hw]
    rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedFillComparison.CM
