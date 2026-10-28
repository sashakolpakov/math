import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidue

/-! # Residue Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.ResidueTotal

noncomputable section

/-! Literal top-coordinate normalization of the mixed point class
after the oriented normal residue. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components
open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientResidue
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (R : Type u) [CommRing R] (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  {c m : ℕ} (U : ULift.{u} (Fin m) → C) (s : Fin c → R) (t : Fin m → R)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))
  (N : Cᵒᵖ ⥤ ModuleCat.{u} R) (α : Fractions.modules R P ⟶ N)
  (hN : ∀ (a : Cᵒᵖ) (i : Fin c) (x : N.obj a), s i • x = 0)

abbrev residueComplex := (single (Cᵒᵖ ⥤ ModuleCat R) (.up ℕ) c).obj N

def map : Components.source R s t ⟶ (AugmentedOrdered.CechFunctor.bicomplex U (residueComplex R (c := c) N)).total (.up ℕ) :=
  Total.map R P U s t ht ≫
    AugmentedOrdered.CechTopNaturality.totalMap U (Koszul.CoefficientResidue.complexMap R P s N α hN)

theorem top : (map R P U s t ht N α hN).f (c + m) =
    Components.component R P U t ht (c + m) c m rfl ≫
      AugmentedOrdered.CechFunctor.objectMap U ((Koszul.CoefficientResidue.complexMap R P s N α hN).f c) m ≫
        (AugmentedOrdered.CechFunctor.bicomplex U (residueComplex R (c := c) N)).ιTotal (.up ℕ) c m (c + m) rfl := by
  change (Total.map R P U s t ht).f (c + m) ≫ _ = _
  rw [TotalTop.top_map, Category.assoc]
  rw [AugmentedOrdered.CechTopNaturality.totalMap, HomologicalComplex₂.ιTotal_map]
  rfl

theorem projection (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m) :
    (map R P U s t ht N α hN).f (c + m) ≫
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (AugmentedOrdered.CechFunctor.bicomplex U (residueComplex R (c := c) N))) c m (c + m) ≫
        Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m =>
          ((residueComplex R (c := c) N).X c).obj (op ((AugmentedOrdered.Cech.formal U m).obj b))) a ≫
            (singleObjXSelf (.up ℕ) c N).hom.app (op ((AugmentedOrdered.Cech.formal U m).obj a)) =
      ModuleCat.ofHom (Components.coordinateAt R P U t ht (c + m) c m rfl a) ≫
        (Koszul.CoefficientResidue.evaluation R P s N α).app (op ((AugmentedOrdered.Cech.formal U m).obj a)) := by
  rw [top]
  have hself := (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_self (AugmentedOrdered.CechFunctor.bicomplex U (residueComplex R (c := c) N))) c m
  simp only [Category.assoc]
  rw [← Category.assoc
    ((AugmentedOrdered.CechFunctor.bicomplex U (residueComplex R (c := c) N)).ιTotal (.up ℕ) c m (c + m) rfl),
    hself, Category.id_comp]
  rw [← Category.assoc (AugmentedOrdered.CechFunctor.objectMap U ((Koszul.CoefficientResidue.complexMap R P s N α hN).f c) m),
    AugmentedOrdered.CechCoordinates.objectMap_comp_pi, Category.assoc,
    ← Category.assoc (Components.component R P U t ht (c + m) c m rfl), Components.component_projection]
  have he := congrArg (fun f => f.app (op ((AugmentedOrdered.Cech.formal U m).obj a)))
    (Koszul.CoefficientResidue.complexMap_top R P s N α hN)
  exact congrArg (ModuleCat.ofHom (Components.coordinateAt R P U t ht (c + m) c m rfl a) ≫ ·) he

theorem coefficient (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m)
    (φ : Module.Dual R (⋀[R]^(c + m) (Fractions.ambient R (c := c) (m := m)))) :
    ((map R P U s t ht N α hN).f (c + m) ≫
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (AugmentedOrdered.CechFunctor.bicomplex U (residueComplex R (c := c) N))) c m (c + m) ≫
        Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m =>
          ((residueComplex R (c := c) N).X c).obj (op ((AugmentedOrdered.Cech.formal U m).obj b))) a ≫
            (singleObjXSelf (.up ℕ) c N).hom.app (op ((AugmentedOrdered.Cech.formal U m).obj a)))
      (show (Components.source R s t).X (c + m) from φ) =
      α.app (op ((AugmentedOrdered.Cech.formal U m).obj a))
        (Fractions.reciprocal R P U t ht a * algebraMap R (P.obj (op ((AugmentedOrdered.Cech.formal U m).obj a)))
          (φ (TopExteriorCoordinates.generator
            (TopResidue.basis R (c := c) (m := m))))) := by
  rw [projection]
  exact Koszul.CoefficientResidue.fraction R P s N α U t ht a φ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.ResidueTotal
