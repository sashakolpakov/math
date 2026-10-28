import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPoint.SupportedLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomPresheafMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SupportedUniqueness

/-! # Duplicate Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateFraction

noncomputable section

/-! The explicit duplicate-parameter lift of the point Koszul complex,
followed by its canonical map to the normal complex, is the genuine
mixed partial fraction, up to cochain homotopy. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable (R : Type u) [CommRing R] {c m : ℕ}
  (s : Fin c → R) (t : Fin m → R)

def pointIso : OrientedTopCohomology.koszul R (Fin.append s t) ≅
    Exterior.KoszulComplex.complex R (KoszulPartial.Fractions.ambient R (c := c) (m := m))
      (KoszulPartial.Differential.equation R s t) :=
  Exterior.KoszulBasisResolution.complexIso R _ _
    (KoszulPartial.TopResidue.basis R).equivFun.symm (by
      simpa only [KoszulPartial.Resolution.basis_values] using
        Exterior.KoszulBasisResolution.equation_basis R
          (KoszulPartial.TopResidue.basis R) (KoszulPartial.Differential.equation R s t))

def normalInclusion : OrientedTopCohomology.koszul R s ⟶
    OrientedTopCohomology.koszul R (Fin.append s t) :=
  KoszulPartial.Resolution.inclusion R s t ≫ (pointIso R s t).inv

theorem normalInclusion_pointIso : normalInclusion R s t ≫ (pointIso R s t).hom =
    KoszulPartial.Resolution.inclusion R s t := by
  simp [normalInclusion]

theorem dual_comp {K L M : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    DualComplexHomology.map R g ≫ DualComplexHomology.map R f =
      DualComplexHomology.map R (f ≫ g) := by
  apply HomologicalComplex.Hom.ext
  funext q
  rfl

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R) (U : ULift.{u} (Fin m) → C)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

def normalMap : KoszulPartial.Components.coefficient R P (Fin.append s t) ⟶ KoszulPartial.Components.coefficient R P s :=
  HomPresheafMap.map R P s (Fin.append s t) (normalInclusion R s t)

def supportedMap : KoszulPartial.Components.source R s t ⟶ (KoszulPartial.Components.target R P U s).total (.up ℕ) :=
  DualComplexHomology.map R (pointIso R s t).hom ≫
    KoszulPoint.SupportedLift.map R s t P U ht (normalMap R s t P)

theorem forget : supportedMap R s t P U ht ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s) =
    KoszulPartial.Total.map R P U s t ht ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s) := by
  dsimp only [supportedMap]
  rw [Category.assoc, KoszulPoint.SupportedLift.map_forget]
  change DualComplexHomology.map R (pointIso R s t).hom ≫
    (KoszulPartial.CanonicalMap.scalarsMap R P (Fin.append s t) ≫
      AugmentedOrdered.CechForgetNaturality.ambientMap
        (HomPresheafMap.map R P s (Fin.append s t) (normalInclusion R s t))) = _
  rw [HomPresheafMap.scalars, ← Category.assoc, dual_comp,
    normalInclusion_pointIso]
  exact (KoszulPartial.CanonicalMap.forget_factorization R P U s t ht).symm

def homotopy : Homotopy (supportedMap R s t P U ht) (KoszulPartial.Total.map R P U s t ht) :=
  SupportedUniqueness.to_partial R P U s t ht _
    (Homotopy.ofEq (forget R s t P U ht))

theorem homology (q : ℕ) : homologyMap (supportedMap R s t P U ht) q =
    homologyMap (KoszulPartial.Total.map R P U s t ht) q :=
  (homotopy R s t P U ht).homologyMap_eq q

theorem class_eq (φ : Module.Dual R (⋀[R]^(c + m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :
    homologyMap (supportedMap R s t P U ht) (c + m)
      (KoszulPartial.PartialClass.sourceClass R s t φ) =
        KoszulPartial.PartialClass.supportedClass R P U s t ht φ := by
  rw [homology, KoszulPartial.PartialClass.supportedClass_eq]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateFraction
