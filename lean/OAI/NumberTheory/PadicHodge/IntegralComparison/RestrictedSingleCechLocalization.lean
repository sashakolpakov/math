import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.Localization
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleCoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechLinear
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Restricted Single Cech Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictedSingleCechLocalization

noncomputable section

/-! Localization detects classes fixed by the source-ring parameter
on the original supported single-degree total, after restriction to
any ambient coefficient ring. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)

local instance restrictionHomology : (ModuleCat.restrictScalars.{u} ρ).PreservesHomology where
  preservesKernels {_ _} f := ModuleCat.preservesLimit_restrictScalars ρ (parallelPair f 0)
  preservesCokernels {_ _} f := ModuleCat.preservesColimit_restrictScalars ρ (parallelPair f 0)

def restriction : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} A) :=
  (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} B) (ModuleCat.{u} A)).obj
    (ModuleCat.restrictScalars ρ)

def functor (c q : ℕ) : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} A :=
  restriction ρ ⋙ single (Cᵒᵖ ⥤ ModuleCat.{u} A) (.up ℕ) c ⋙
    Supported.CechHomotopyEquivalence.functor U q

instance functor_additive (c q : ℕ) : (functor ρ U c q).Additive := by
  dsimp only [functor, restriction]
  infer_instance

def coordinateIso (P : Cᵒᵖ ⥤ ModuleCat.{u} B) (c n : ℕ) :
    (functor ρ U c (n+c)).obj P ≅
      (ModuleCat.restrictScalars ρ).obj ((AugmentedOrdered.Cech.complex U P).homology n) :=
  IntegralComparison.Functor.SingleTotal.homologyIso (AugmentedOrdered.CechFunctor.functor U)
    (P ⋙ ModuleCat.restrictScalars ρ) c n ≪≫
      (AugmentedCech.CoefficientCohomology.Change.homologyIso U (ModuleCat.restrictScalars ρ) P n).symm

theorem map_eq {P Q : Cᵒᵖ ⥤ ModuleCat.{u} B} (α : P ⟶ Q) (c n : ℕ) :
    (functor ρ U c (n+c)).map α =
      homologyMap (IntegralComparison.Functor.SingleCoefficientNaturality.totalMap
        (AugmentedOrdered.CechFunctor.functor U)
        (Functor.whiskerRight α (ModuleCat.restrictScalars ρ)) c) (n+c) := rfl

@[reassoc]
theorem naturality {P Q : Cᵒᵖ ⥤ ModuleCat.{u} B} (α : P ⟶ Q) (c n : ℕ) :
    (functor ρ U c (n+c)).map α ≫ (coordinateIso ρ U Q c n).hom =
      (coordinateIso ρ U P c n).hom ≫
        (ModuleCat.restrictScalars ρ).map (homologyMap (AugmentedOrdered.CechFunctor.complexMap U α) n) := by
  rw [map_eq]
  have hs := IntegralComparison.Functor.SingleCoefficientNaturality.homology_naturality
    (AugmentedOrdered.CechFunctor.functor U) (Functor.whiskerRight α (ModuleCat.restrictScalars ρ)) c n
  have hc := AugmentedCech.CoefficientCohomology.Change.homology_naturality U
    (ModuleCat.restrictScalars ρ) P α n
  have hi := CohomologyConcentrationNaturality.inverse_square _ _
    (AugmentedCech.CoefficientCohomology.Change.homologyIso U (ModuleCat.restrictScalars ρ) P n)
    (AugmentedCech.CoefficientCohomology.Change.homologyIso U (ModuleCat.restrictScalars ρ) Q n) hc
  simpa only [coordinateIso, Iso.trans_hom, Iso.symm_hom, Category.assoc] using
    DualComplexHomology.compose_squares _ _ _ _ _ _ _ hs hi

def coordinate (P : Cᵒᵖ ⥤ ModuleCat.{u} B) (c n : ℕ)
    (x : (functor ρ U c (n+c)).obj P) : (AugmentedOrdered.Cech.complex U P).homology n :=
  (coordinateIso ρ U P c n).hom x

theorem coordinate_injective (P : Cᵒᵖ ⥤ ModuleCat.{u} B) (c n : ℕ) :
    Function.Injective (coordinate ρ U P c n) :=
  (ConcreteCategory.bijective_of_isIso (coordinateIso ρ U P c n).hom).injective

theorem coordinate_naturality {P Q : Cᵒᵖ ⥤ ModuleCat.{u} B} (α : P ⟶ Q) (c n : ℕ)
    (x : (functor ρ U c (n+c)).obj P) :
    coordinate ρ U Q c n ((functor ρ U c (n+c)).map α x) =
      homologyMap (AugmentedOrdered.CechFunctor.complexMap U α) n (coordinate ρ U P c n x) :=
  ConcreteCategory.congr_hom (naturality ρ U α c n) x

theorem scalar_homology (P : Cᵒᵖ ⥤ ModuleCat.{u} B) (n : ℕ) (z : B) :
    homologyMap (AugmentedOrdered.CechFunctor.complexMap U (z • 𝟙 P)) n = z • 𝟙 ((AugmentedOrdered.Cech.complex U P).homology n) := by
  change (AugmentedOrdered.CechLinear.cohomology U B n).map (z • 𝟙 P) = _
  rw [AugmentedOrdered.CechLinear.cohomology_smul, CategoryTheory.Functor.map_id]
  rfl

theorem coordinate_scalar (P : Cᵒᵖ ⥤ ModuleCat.{u} B) (c n : ℕ) (z : B)
    (x : (functor ρ U c (n+c)).obj P) :
    coordinate ρ U P c n ((functor ρ U c (n+c)).map (z • 𝟙 P) x) =
      z • coordinate ρ U P c n x := by
  rw [coordinate_naturality, scalar_homology]
  rfl

variable [Finite ι] {P Q : Cᵒᵖ ⥤ ModuleCat.{u} B} (α : P ⟶ Q) (z : B)
  (hsurj : ∀ j (y : Q.obj j), ∃ (a : ℕ) (x : P.obj j), z^a • y = α.app j x)
  (hker : ∀ j (x : P.obj j), α.app j x = 0 → ∃ a : ℕ, z^a • x = 0)

include hsurj hker in
theorem eq_of_map_eq (c n : ℕ) (x y : (functor ρ U c (n+c)).obj P)
    (hx : (functor ρ U c (n+c)).map (z • 𝟙 P) x = x)
    (hy : (functor ρ U c (n+c)).map (z • 𝟙 P) y = y)
    (h : (functor ρ U c (n+c)).map α x = (functor ρ U c (n+c)).map α y) : x = y := by
  apply coordinate_injective ρ U P c n
  apply AugmentedCech.Localization.eq_of_map_eq U α z hsurj hker n
  · exact (coordinate_scalar ρ U P c n z x).symm.trans
      (congrArg (coordinate ρ U P c n) hx)
  · exact (coordinate_scalar ρ U P c n z y).symm.trans
      (congrArg (coordinate ρ U P c n) hy)
  · have h' := congrArg (coordinate ρ U Q c n) h
    simpa only [coordinate_naturality] using h'

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictedSingleCechLocalization
