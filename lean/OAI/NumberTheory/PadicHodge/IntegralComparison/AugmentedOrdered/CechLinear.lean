import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Cech Linear -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLinear

noncomputable section

/-! The actual augmented ordered Čech complex preserves ambient
scalars, including its canonical cohomology maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C) (R : Type u) [CommRing R]

instance linear : (CechFunctor.functor U (D := ModuleCat.{u} R)).Linear R where
  map_smul {P Q} f r := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (Limits.Pi.map (fun a : Cech.Index ι n => (r • f).app (op ((Cech.formal U n).obj a)))) =
      r • (Limits.Pi.map (fun a : Cech.Index ι n => f.app (op ((Cech.formal U n).obj a))))
    apply Pi.hom_ext
    intro a
    rw [Pi.map_π, Linear.smul_comp, Pi.map_π]
    rfl

def cohomology (q : ℕ) : (Cᵒᵖ ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  CechFunctor.functor U ⋙ homologyFunctor (ModuleCat R) (.up ℕ) q

instance cohomology_additive (q : ℕ) : (cohomology U R q).Additive := by
  dsimp only [cohomology]
  infer_instance

theorem cohomology_smul (q : ℕ) {P Q : Cᵒᵖ ⥤ ModuleCat.{u} R} (r : R) (f : P ⟶ Q) :
    (cohomology U R q).map (r • f) = r • (cohomology U R q).map f := by
  change homologyMap ((CechFunctor.functor U).map (r • f)) q = r • homologyMap ((CechFunctor.functor U).map f) q
  rw [(CechFunctor.functor U).map_smul, Resolution.CohomologyMaps.homologyMap_smul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechLinear
