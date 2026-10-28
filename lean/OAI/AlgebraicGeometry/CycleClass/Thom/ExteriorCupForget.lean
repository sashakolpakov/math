import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupForget
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality

/-! # Exterior Cup Forget -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget.Constructions

noncomputable section

/-! Forgetting supports in the actual exterior cup gives the ordinary cup
of the actual projection pullbacks, with all degree transports explicit. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportCupForget.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even
open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem relativeInclusion_pullback {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n a) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) Y B n a) :=
  ConcreteCategory.congr_hom (Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) f hf n) a

theorem twoSupportCup_forget (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X (A ∪ B) (p + q)
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b) =
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) X p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A p a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X B q b) := by
  have h := relativeInclusion_pullback (𝟙 X) (Set.subset_union_right : B ⊆ A ∪ B) (p + q)
    (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b)
  rw [HodgeConjecture.DegreeTwo.SupportCupForget.Constructions.twoSupportCohomologyCup_forget_left X A B hA hB p q a b,
    Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup_inclusion, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id,
    ConcreteCategory.id_apply] at h
  exact h.symm

theorem relativeExteriorCup_forget (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (p + q) (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a b) =
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (TopCat.of (X × Y)) p q
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst p
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A p a))
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd q
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) Y B q b)) := by
  have h := twoSupportCup_forget (TopCat.of (X × Y)) (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B)
    (hA.preimage continuous_fst) (hB.preimage continuous_snd) p q
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst : TopCat.of (X × Y) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p a)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodSnd : TopCat.of (X × Y) ⟶ Y)
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q b)
  rw [relativeInclusion_pullback, relativeInclusion_pullback] at h
  exact h

theorem relativeInclusion_supportCast (X : TopCat.{0}) {A B : Set X} (h : A = B) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X B n
      (eqToHom (congrArg (fun U => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X U n) h) a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A n a := by
  subst h
  rfl

theorem relativeInclusion_degreeCast (X : TopCat.{0}) (A : Set X) {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A m
      (eqToHom (congrArg (fun j => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A j) h) a) =
    eqToHom (congrArg (fun j => (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).homology j) h)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A n a) := by
  subst h
  rfl

def evenAbsoluteExteriorCup (X Y : TopCat.{0}) (p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).homology (2 * p))
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) Y).homology (2 * q)) :
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y))).homology (2 * (p + q)) :=
  eqToHom (congrArg (fun n =>
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y))).homology n)
    (Nat.mul_add 2 p q).symm)
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (TopCat.of (X × Y)) (2 * p) (2 * q)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst (2 * p) a)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd (2 * q) b))

theorem evenExteriorCup_forget (X Y : TopCat.{0}) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (2 * (p + q)) (ExteriorImageCup.Constructions.Even.evenExteriorCup X Y A B hA hB p q a b) =
    evenAbsoluteExteriorCup X Y p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A (2 * p) a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) Y B (2 * q) b) := by
  unfold ExteriorImageCup.Constructions.Even.evenExteriorCup evenAbsoluteExteriorCup
  rw [relativeInclusion_degreeCast _ _ (Nat.mul_add 2 p q).symm,
    relativeExteriorCup_forget X Y A B hA hB (2 * p) (2 * q) a b]

theorem imageExteriorCup_forget {M N M' N' : Type}
    [TopologicalSpace N] [TopologicalSpace N'] (u : M → N) (v : M' → N')
    (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range v)ᶜ (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (N × N'))
      (Set.range (Prod.map u v))ᶜ (2 * (p + q)) (ExteriorImageCup.Constructions.imageExteriorCup u v hu hv p q a b) =
    evenAbsoluteExteriorCup (TopCat.of N) (TopCat.of N') p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p) a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of N') (Set.range v)ᶜ (2 * q) b) := by
  unfold ExteriorImageCup.Constructions.imageExteriorCup
  rw [relativeInclusion_supportCast _ (ExteriorImageCup.Constructions.crossSupportComplement_range u v)]
  exact evenExteriorCup_forget (TopCat.of N) (TopCat.of N') (Set.range u)ᶜ (Set.range v)ᶜ hu hv p q a b

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget.Constructions
