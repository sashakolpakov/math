import OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees

/-! # Even Intersection Associativity -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions

/-! Associativity of the actual intersection cup in the original
twice-codimension grading, with the literal support reassociation. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleDiagonalCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem evenIntersectionCup_eq_cupAt (X : TopCat) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B (2 * q)) :
    Normal.IntersectionCup.Constructions.evenIntersectionCup X A B hA hB p q a b =
      SupportedCupDegrees.Constructions.cupAt X A B hA hB (2 * p) (2 * q) (2 * (p + q)) (Nat.mul_add 2 p q).symm a b :=
  Intersection.TwoSupportCup.Constructions.evenIntersectionCup_eq_twoSupport X A B hA hB p q a b

theorem evenIntersectionCup_associative (X : TopCat) (A B C : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B (2 * q))
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C (2 * r)) :
    eqToHom (congrArg (fun d => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X ((A ∪ B) ∪ C) (2 * d))
      (Nat.add_assoc p q r))
      (Normal.IntersectionCup.Constructions.evenIntersectionCup X (A ∪ B) C (hA.union hB) hC (p + q) r
        (Normal.IntersectionCup.Constructions.evenIntersectionCup X A B hA hB p q a b) c) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (TripleDiagonalCup.Constructions.unionAssociate_mapsTo X A B C) (2 * (p + (q + r)))
        (Normal.IntersectionCup.Constructions.evenIntersectionCup X A (B ∪ C) hA (hB.union hC) p (q + r) a
          (Normal.IntersectionCup.Constructions.evenIntersectionCup X B C hB hC q r b c)) := by
  simp_rw [evenIntersectionCup_eq_cupAt]
  have he := SupportedCupDegrees.Constructions.cupAt_cast_output X (A ∪ B) C (hA.union hB) hC
    (2 * (p + q)) (2 * r) (2 * ((p + q) + r)) (2 * (p + (q + r)))
    (Nat.mul_add 2 (p + q) r).symm (congrArg (fun n => 2 * n) (Nat.add_assoc p q r))
    (SupportedCupDegrees.Constructions.cupAt X A B hA hB (2 * p) (2 * q) (2 * (p + q)) (Nat.mul_add 2 p q).symm a b) c
  exact he.trans (SupportedCupDegrees.Constructions.cupAt_associative X A B C hA hB hC
    (2 * p) (2 * q) (2 * r) (2 * (p + q)) (2 * (q + r)) (2 * (p + (q + r)))
    (Nat.mul_add 2 p q).symm (Nat.mul_add 2 q r).symm (Nat.mul_add 2 p (q + r)).symm (by omega) a b c)

end AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets

/-! The actual supported cup with explicitly identified output
complement and degree. This keeps intersection complements literal
when composing geometric section steps. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportedCupDegrees.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleDiagonalCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem id_mapsTo_eq (X : TopCat) (A B : Set X) (h : A = B) : Set.MapsTo (𝟙 X) A B :=
  fun _ hx => h ▸ hx

theorem relativeMap_id_eqToHom (X : TopCat) (A B : Set X) (h : A = B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) (id_mapsTo_eq X A B h) n =
      eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) h.symm) := by
  cases h
  exact AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) X A n

def cupTo (X : TopCat) (A B S : Set X) (hA : IsOpen A) (hB : IsOpen B) (hS : A ∪ B = S)
    (p q n : ℕ) (hn : p + q = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n :=
  eqToHom (congrArg (fun T => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X T n) hS)
    (SupportedCupDegrees.Constructions.cupAt X A B hA hB p q n hn a b)

theorem cupTo_associative (X : TopCat) (A B C AB BC ABC : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hAB : IsOpen AB) (hBC : IsOpen BC)
    (eAB : A ∪ B = AB) (eBC : B ∪ C = BC) (eL : AB ∪ C = ABC) (eR : A ∪ BC = ABC)
    (p q r m l n : ℕ) (hm : p + q = m) (hl : q + r = l) (hn : p + l = n) (hmr : m + r = n)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X C r) :
    cupTo X AB C ABC hAB hC eL m r n hmr (cupTo X A B AB hA hB eAB p q m hm a b) c =
      cupTo X A BC ABC hA hBC eR p l n hn a (cupTo X B C BC hB hC eBC q r l hl b c) := by
  cases eAB
  cases eBC
  cases eR
  have h := SupportedCupDegrees.Constructions.cupAt_associative X A B C hA hB hC p q r m l n hm hl hn hmr a b c
  have he := relativeMap_id_eqToHom X ((A ∪ B) ∪ C) (A ∪ (B ∪ C)) (Set.union_assoc A B C) n
  rw [he] at h
  have hc := congrArg (eqToHom (congrArg
    (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) (Set.union_assoc A B C))) h
  simpa only [cupTo, eqToHom_refl, ConcreteCategory.id_apply,
    ← ConcreteCategory.comp_apply, eqToHom_trans] using hc

theorem imageIntersectionCup_eq_cupTo {M N P : Type} [TopologicalSpace N] (u : M → N) (v : P → N)
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)) :
    ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b =
      cupTo (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ (Set.range u ∩ Set.range v)ᶜ hu hv
        (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u v) (2 * p) (2 * q) (2 * (p + q)) (Nat.mul_add 2 p q).symm a b :=
  (ImageIntersectionTo.Constructions.Normal.imageIntersectionCup_eq_even u v hu hv p q a b).trans
    (congrArg (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) S
      (2 * (p + q))) (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u v))) (evenIntersectionCup_eq_cupAt _ _ _ hu hv p q a b))

end AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets

end

end OAI
