import OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity

/-! # Cup Degrees -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupDegrees.Constructions

noncomputable section

/-! Normal-coordinate multiplication with an independently specified
total dimension, allowing literal head-and-tail coordinate vectors. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat} {A B : Set X} {p q m : ℕ}
  (f : X ⟶ TopCat.of (Fin p → ℂ)) (g : X ⟶ TopCat.of (Fin q → ℂ))
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin m → ℂ))

def normalMapAt : X ⟶ TopCat.of (Fin m → ℂ) :=
  TopCat.ofHom ⟨fun x => e (f x, g x), e.continuous.comp (f.hom.continuous.prodMk g.hom.continuous)⟩

theorem normalMapAt_mapsTo (hf : Set.MapsTo f A ({0}ᶜ)) (hg : Set.MapsTo g B ({0}ᶜ)) :
    Set.MapsTo (normalMapAt f g e) (A ∪ B) ({0}ᶜ) := by
  intro x hx hz
  have hzero : (f x, g x) = 0 := e.injective (by exact hz.trans (map_zero e).symm)
  rcases hx with hx | hx
  · exact hf hx (congrArg Prod.fst hzero)
  · exact hg hx (congrArg Prod.snd hzero)

theorem normalCupAt (hA : IsOpen A) (hB : IsOpen B) (h : p + q = m)
    (hf : Set.MapsTo f A ({0}ᶜ)) (hg : Set.MapsTo g B ({0}ᶜ)) :
    SupportedCupDegrees.Constructions.cupAt X A B hA hB (2 * p) (2 * q) (2 * m) ((Nat.mul_add 2 p q).symm.trans (congrArg (fun n => 2 * n) h))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalMapAt f g e) (normalMapAt_mapsTo f g e hf hg)
      (2 * m) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass m) := by
  cases h
  exact (EvenIntersectionAssociativity.Constructions.evenIntersectionCup_eq_cupAt X A B hA hB p q _ _).symm.trans
    (IntersectionCup.Constructions.evenIntersectionCup_normalized_pullbacks f g hf hg e hA hB)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.CupDegrees.Constructions
