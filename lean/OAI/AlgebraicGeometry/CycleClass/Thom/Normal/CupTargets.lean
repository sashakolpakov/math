import OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupDegrees

/-! # Cup Targets -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupTargets.Constructions

noncomputable section

/-! Normal-coordinate multiplication in a literally specified output
support complement and total dimension. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem normalCupTo {X : TopCat} (A B S : Set X) (hA : IsOpen A) (hB : IsOpen B) (hS : A ∪ B = S)
    (p q m : ℕ) (hm : p + q = m)
    (f : X ⟶ TopCat.of (Fin p → ℂ)) (g : X ⟶ TopCat.of (Fin q → ℂ))
    (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin m → ℂ))
    (hf : Set.MapsTo f A ({0}ᶜ)) (hg : Set.MapsTo g B ({0}ᶜ))
    (hfg : Set.MapsTo (CupDegrees.Constructions.normalMapAt f g e) S ({0}ᶜ)) :
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo X A B S hA hB hS (2 * p) (2 * q) (2 * m)
      ((Nat.mul_add 2 p q).symm.trans (congrArg (fun n => 2 * n) hm))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CupDegrees.Constructions.normalMapAt f g e) hfg (2 * m)
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass m) :=
  (congrArg (eqToHom (congrArg (fun T => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X T (2 * m)) hS))
    (CupDegrees.Constructions.normalCupAt f g e hA hB hm hf hg)).trans
      (ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast (CupDegrees.Constructions.normalMapAt f g e) hS (CupDegrees.Constructions.normalMapAt_mapsTo f g e hf hg) hfg
        (2 * m) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass m))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupTargets.Constructions
