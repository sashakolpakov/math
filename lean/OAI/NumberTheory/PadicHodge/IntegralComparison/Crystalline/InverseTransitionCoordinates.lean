import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CohomologyDifference
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.PresheafExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyTransport

/-! # Inverse Transition Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseTransitionCoordinates

noncomputable section

/-! The original inverse-system transitions are exactly the original bounded-level Ext pullback maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedProductCohomology

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.resolution (p := p) (J := J) (δ := δ) f

theorem componentMap (n m : ℕ) (hnm : n ≤ m) :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
      (CohomologyDifference.componentTransition (p := p) (J := J) (δ := δ) f n m hnm) =
        BoundedLevel.FramePresheafRestriction.restriction f n m hnm I := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem levelHomologyIso (n i : ℕ) :
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (BoundedProductCohomology.levelIso (p := p) (J := J) (δ := δ) f n) =
      Iso.refl _ :=
  Functor.mapIso_refl _ _

theorem componentEquiv (n i : ℕ) : BoundedProductCohomology.componentLinearEquiv (p := p) (J := J) (δ := δ) f n i =
    (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R (BoundedProductCohomology.component f n) i).trans
      (BoundedResolutionLevels.homologyIso f n i).toLinearEquiv := by
  simp only [BoundedProductCohomology.componentLinearEquiv, BoundedProductCohomology.componentHomologyIso, levelHomologyIso]
  rfl

theorem homology (n m : ℕ) (hnm : n ≤ m) (i : ℕ) : HomologicalComplex.homologyMap
    (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
      (CohomologyDifference.componentTransition (p := p) (J := J) (δ := δ) f n m hnm)) i ≫
        (BoundedResolutionLevels.homologyIso f n i).hom =
      (BoundedResolutionLevels.homologyIso f m i).hom ≫
        ModuleCat.ofHom (Bounded.CohomologyTransition.map f n m hnm i) :=
  (congrArg (fun a => HomologicalComplex.homologyMap a i ≫
    (BoundedResolutionLevels.homologyIso f n i).hom) (componentMap f n m hnm)).trans
      (BoundedLevel.PresheafExt.homology f n m hnm I i)

theorem naturality (n m : ℕ) (hnm : n ≤ m) (i : ℕ) (x : (BoundedProductCohomology.component (p := p) (J := J) (δ := δ) f m).homology i) :
    BoundedProductCohomology.componentLinearEquiv f n i
      (HomologicalComplex.homologyMap (CohomologyDifference.componentTransition f n m hnm) i x) =
        Bounded.CohomologyTransition.map f n m hnm i (BoundedProductCohomology.componentLinearEquiv f m i x) := by
  let g := ModuleCat.ofHom (Bounded.CohomologyTransition.map (p := p) (J := J) (δ := δ) f n m hnm i)
  have h := InverseTransitionCoordinates.homology (p := p) (J := J) (δ := δ) f n m hnm i
  have ht := Lifted.HomologyTransport.naturality.{u + 1, u + 1, u + 2} R
    (CohomologyDifference.componentTransition f n m hnm) i
    (BoundedResolutionLevels.homologyIso f m i)
    (BoundedResolutionLevels.homologyIso f n i) g h x
  exact (congrArg (fun e => e (HomologicalComplex.homologyMap
    (CohomologyDifference.componentTransition f n m hnm) i x)) (componentEquiv f n i)).trans
      (ht.trans (congrArg g (congrArg (fun e => e x) (componentEquiv f m i).symm)))

theorem transition (n i : ℕ) : CohomologyDifference.transition (p := p) (J := J) (δ := δ) f n i =
    Bounded.CohomologyTransition.map f n (n + 1) (Nat.le_succ n) i := by
  apply LinearMap.ext
  intro x
  exact (naturality f n (n + 1) (Nat.le_succ n) i ((BoundedProductCohomology.componentLinearEquiv f (n + 1) i).symm x)).trans
    (congrArg (Bounded.CohomologyTransition.map f n (n + 1) (Nat.le_succ n) i)
      ((BoundedProductCohomology.componentLinearEquiv f (n + 1) i).apply_symm_apply x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.InverseTransitionCoordinates
