import OAI.NumberTheory.PadicHodge.IntegralComparison.CommAlgebraicCechPairing

/-! # Comm Algebraic Cech Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CommAlgebraicCechCohomology.Pairing

noncomputable section

/-! The canonical algebra-to-module Čech comparison preserves cup
products on the actual categorical cohomology groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality

universe u v w t r

variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  [HasProducts.{w} (CommAlgCat.{max w t} R)]
  [PreservesLimitsOfSize.{w, w} (CommAlgebraicCechPairing.forgetModule.{max w t, r} (R := R))]
  (N : SimplicialObject (FormalCoproduct.{w} C)) (P : Cᵒᵖ ⥤ CommAlgCat.{max w t} R)

local instance moduleProductsCohomology : HasProducts.{w} (ModuleCat.{max w t} R) :=
  fun T => (ModuleCat.hasLimitsOfSize.{w, w, max w t, r}).has_limits_of_shape (Discrete T)

theorem cohomology_cup (p q : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (CommAlgebraicCechPairing.algebraObject.{u, v, w, t, r} N P)).homology p)
    (y : (Cosimplicial.ModuleComplex.complex (CommAlgebraicCechPairing.algebraObject.{u, v, w, t, r} N P)).homology q) :
    HomologicalComplex.homologyMap (CommAlgebraicCechPairing.complexIso.{u, v, w, t, r} N P).hom (p + q)
      (Cosimplicial.ModuleCup.cohomologyCup (CommAlgebraicCechPairing.algebraObject.{u, v, w, t, r} N P) p q x y) =
        Presheaf.AugmentationCohomology.Product.sourceCohomologyCup N (CommAlgebraicCechPairing.modulePresheaf.{u, v, max w t, r} P)
          (CommAlgebraicCechPairing.multiplication.{u, v, max w t, r} P) (CommAlgebraicCechPairing.multiplication_natural.{u, v, max w t, r} P) p q
          (HomologicalComplex.homologyMap (CommAlgebraicCechPairing.complexIso.{u, v, w, t, r} N P).hom p x)
          (HomologicalComplex.homologyMap (CommAlgebraicCechPairing.complexIso.{u, v, w, t, r} N P).hom q y) := by
  obtain ⟨x, rfl⟩ := Module.CochainClasses.classMap_surjective
    (Cosimplicial.ModuleComplex.complex (CommAlgebraicCechPairing.algebraObject.{u, v, w, t, r} N P)) p x
  obtain ⟨y, rfl⟩ := Module.CochainClasses.classMap_surjective
    (Cosimplicial.ModuleComplex.complex (CommAlgebraicCechPairing.algebraObject.{u, v, w, t, r} N P)) q y
  rw [Cosimplicial.ModuleCup.cup_class]
  erw [← Module.CochainClassNaturality.naturality_apply (CommAlgebraicCechPairing.complexIso.{u, v, w, t, r} N P).hom (p + q),
    ← Module.CochainClassNaturality.naturality_apply (CommAlgebraicCechPairing.complexIso.{u, v, w, t, r} N P).hom p,
    ← Module.CochainClassNaturality.naturality_apply (CommAlgebraicCechPairing.complexIso.{u, v, w, t, r} N P).hom q]
  unfold Presheaf.AugmentationCohomology.Product.sourceCohomologyCup
  erw [Cochain.CohomologyCup.cup_class]
  apply congrArg (Module.CochainClasses.classMap _ (p + q))
  apply Subtype.ext
  exact CommAlgebraicCechPairing.cochain_cup.{u, v, w, t, r} N P p q x.val y.val

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CommAlgebraicCechCohomology.Pairing
