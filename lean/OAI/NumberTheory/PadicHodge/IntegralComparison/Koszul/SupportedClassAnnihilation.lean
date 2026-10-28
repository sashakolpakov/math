import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.FractionQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechHomotopyEquivalence

/-! # Supported Class Annihilation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedClassAnnihilation

noncomputable section

/-! Every supported mixed point fraction is annihilated by the actual
point ideal, before any residue, form symbol, or global comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (φ : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m))))
  (a : R) (ha : a ∈ OrientedTopCohomology.ideal R (Fin.append s t))

include ha in
theorem annihilated : a • KoszulPartial.PartialClass.supportedClass R P U s t ht φ = 0 := by
  have ha' : Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) a =
      Ideal.Quotient.mk (OrientedTopCohomology.ideal R (Fin.append s t)) 0 := by
    simpa only [map_zero] using (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  have h0 := FractionQuotient.weighted_eq R s t P U ht a 0 ha'
  rw [zero_smul] at h0
  rw [ScalarPartialClass.functional R φ,
    ScalarPartialClass.supportedClass_smul, smul_comm a, h0, smul_zero]

include ha in
theorem map_annihilated {V : ModuleCat.{u} R}
    (f : (Supported.CechHomotopyEquivalence.functor U (c+m)).obj (KoszulPartial.Components.coefficient R P s) ⟶ V) :
    a • f (KoszulPartial.PartialClass.supportedClass R P U s t ht φ) = 0 := by
  rw [← f.hom.map_smul, annihilated R P U s t ht φ a ha, map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedClassAnnihilation
