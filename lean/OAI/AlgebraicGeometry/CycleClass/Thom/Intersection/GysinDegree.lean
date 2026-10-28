import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin
import OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity

/-! # Gysin Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.GysinDegree.Constructions

noncomputable section

/-! The genuine supported Thom isomorphism and its cup formula with
an independently specified total codimension. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cupTo_cast_output (X : TopCat) (A B S : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (eS : A ∪ B = S) (p q n m : ℕ) (hn : p + q = n) (hm : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    eqToHom (congrArg (fun d => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S d) hm)
      (EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo X A B S hA hB eS p q n hn a b) =
      EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo X A B S hA hB eS p q m (hn.trans hm) a b := by
  cases hm
  rfl

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) V.analyticSpace
    (Set.range Z.regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)
  {L : Type} (v : L → V.analyticSpace) (hv : IsOpen (Set.range v)ᶜ)
  (d : ℕ) (hd : p + q = d)

def intersectionGysinAt :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Z.regularAnalyticSpace
      (Z.regularComplementInclusion ⁻¹' (Set.range v)ᶜ) (2 * q) ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range Z.regularComplementInclusion ∩ Set.range v)ᶜ (2 * d) :=
  Gysin.Constructions.intersectionGysinIso Z a ha v hv ≪≫ eqToIso
    (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range Z.regularComplementInclusion ∩ Set.range v)ᶜ (2 * n)) hd)

theorem cupTo_eq_gysinAt_pullback
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace (Set.range v)ᶜ (2 * q)) :
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo V.analyticSpace (Set.range Z.regularComplementInclusion)ᶜ (Set.range v)ᶜ
      (Set.range Z.regularComplementInclusion ∩ Set.range v)ᶜ Z.closed.isClosed_range.isOpen_compl hv
      (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq Z.regularComplementInclusion v)
      (2 * p) (2 * q) (2 * d) (by omega) Z.regularThomClass b =
      (intersectionGysinAt Z a ha v hv d hd).hom
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) Z.regularComplementTopCatMap
          (A := Z.regularComplementInclusion ⁻¹' (Set.range v)ᶜ) (B := (Set.range v)ᶜ)
          (fun _ hx => hx) (2 * q) b) := by
  cases hd
  have h := Gysin.Constructions.imageIntersectionCup_eq_gysin_pullback Z a ha v hv b
  rw [EvenIntersectionAssociativity.Constructions.SupportedCupTargets.imageIntersectionCup_eq_cupTo] at h
  simpa only [intersectionGysinAt, eqToIso_refl, Iso.trans_refl] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.GysinDegree.Constructions
