import OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.CanonicalMap

/-! # Duplicate Supported Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateSupportedLift

noncomputable section

/-! An explicit supported lift for a Koszul complex when the support
parameters are already among its equations. The duplicate equations
are folded back before applying the genuine partial-fraction map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
variable (R : Type u) [CommRing R] {n m : ℕ}
  (s : Fin n → R) (t : Fin m → R)
  (a : (Fin m → R) →ₗ[R] (Fin n → R))
  (ha : (GeneratorMatrix.equation R s).comp a =
    GeneratorMatrix.equation R t)

def fold : ((Fin n → R) × (Fin m → R)) →ₗ[R] (Fin n → R) :=
  LinearMap.coprod LinearMap.id a

theorem fold_inl : (fold R a).comp (LinearMap.inl R _ _) = LinearMap.id := by
  ext x i
  simp [fold]

include ha in
theorem equation_fold : (GeneratorMatrix.equation R s).comp (fold R a) =
    KoszulPartial.Differential.equation R s t := by
  apply LinearMap.ext
  intro x
  change GeneratorMatrix.equation R s (x.1 + a x.2) = _
  rw [map_add, show GeneratorMatrix.equation R s (a x.2) =
    GeneratorMatrix.equation R t x.2 from LinearMap.congr_fun ha x.2]
  rfl

def foldMap : Exterior.KoszulComplex.complex R (KoszulPartial.Fractions.ambient R (c := n) (m := m))
    (KoszulPartial.Differential.equation R s t) ⟶
      OrientedTopCohomology.koszul R s :=
  Exterior.KoszulComplex.map R _ _ _ _ (fold R a) (equation_fold R s t a ha)

theorem inclusion_fold : KoszulPartial.Resolution.inclusion R s t ≫ foldMap R s t a ha =
    𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  change (exteriorPower.map q (fold R a)).comp
    (exteriorPower.map q (LinearMap.inl R _ _)) = LinearMap.id
  rw [← exteriorPower.map_comp, fold_inl, exteriorPower.map_id]

theorem dual_inclusion_fold :
    DualComplexHomology.map R (foldMap R s t a ha) ≫
      DualComplexHomology.map R (KoszulPartial.Resolution.inclusion R s t) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change Module.Dual R (⋀[R]^q (Fin n → R)) at φ
  change (⋀[R]^q (Fin n → R)) at x
  change φ ((exteriorPower.map q (fold R a))
    ((exteriorPower.map q (LinearMap.inl R _ _)) x)) = φ x
  apply congrArg φ
  have he : (exteriorPower.map q (fold R a)).comp
      (exteriorPower.map q (LinearMap.inl R _ _)) = LinearMap.id := by
    rw [← exteriorPower.map_comp, fold_inl, exteriorPower.map_id]
  exact LinearMap.congr_fun he x

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R) (U : ULift.{u} (Fin m) → C)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

def lift : DualComplexHomology.complex R (OrientedTopCohomology.koszul R s) ⟶
    (KoszulPartial.Components.target R P U s).total (.up ℕ) :=
  DualComplexHomology.map R (foldMap R s t a ha) ≫
    KoszulPartial.Total.map R P U s t ht

@[reassoc]
theorem lift_forget : lift R s t a ha P U ht ≫ AugmentedOrdered.CechForget.forgetSupport U (KoszulPartial.Components.coefficient R P s) =
    KoszulPartial.CanonicalMap.scalarsMap R P s := by
  dsimp only [lift]
  rw [Category.assoc]
  change DualComplexHomology.map R (foldMap R s t a ha) ≫
    KoszulPartial.Forget.ambientMap R P U s t ht = _
  rw [KoszulPartial.CanonicalMap.forget_factorization, ← Category.assoc,
    dual_inclusion_fold, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.DuplicateSupportedLift
