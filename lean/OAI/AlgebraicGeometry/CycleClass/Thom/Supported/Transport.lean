import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionCup
import OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup

/-! # Transport -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.ProjectionRightCup

/-! Compact-fiber projection also respects cup multiplication on the right by an even-degree base class, with the actual support and degree transports displayed. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallSwap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallCupReversal.Constructions.TwoSupportCommutativity OAI.AlgebraicGeometry.CycleClass.Thom.Projection.CupEnlargement.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def cupSwapTransport (X : TopCat.{0}) (A B : Set X) (p q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (B ∪ A) (q + p) →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) (p + q) :=
  (eqToHom (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) k)
    (Nat.add_comm q p))).hom.comp (HomologicalComplex.homologyMap (BinarySmallSwap.Constructions.unionSwap X A B) (q + p)).hom

theorem evenCup_swap (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    cupSwapTransport X A B (2 * p) q (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X B A hB hA q (2 * p) b a) =
      HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB (2 * p) q a b :=
  (BinarySmallCupReversal.Constructions.TwoSupportCommutativity.twoSupportCup_even_comm X A B hA hB p q a b).symm

def basePullback (X Z : TopCat.{0}) (A : Set X) (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Z)) (Prod.fst ⁻¹' A) p :=
  (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst : TopCat.of (X × Z) ⟶ X)
    (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p).hom

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem projectComplement_rightCup (X : TopCat.{0}) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (K : Set M) (hK : IsCompact K)
    (D : Set (X × M)) (hD : IsOpen D)
    (hbound : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X (TopCat.of M) B Kᶜ ⊆ D) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × M)) D (q + 2 * d)) :
    ProjectionCup.Constructions.projectComplement d X (A ∪ B) K hK (Prod.fst ⁻¹' A ∪ D)
      (Projection.CupEnlargement.Constructions.projectCupBound X (TopCat.of M) A B Kᶜ D hbound)
      (2 * p + q) (2 * p + (q + 2 * d)) (Nat.add_assoc (2 * p) q (2 * d))
      (cupSwapTransport (TopCat.of (X × M)) (Prod.fst ⁻¹' A) D (2 * p) (q + 2 * d)
        (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of (X × M)) D (Prod.fst ⁻¹' A)
          hD (hA.preimage continuous_fst) (q + 2 * d) (2 * p) c
          (basePullback X (TopCat.of M) A (2 * p) a))) =
      cupSwapTransport X A B (2 * p) q
        (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X B A hB hA q (2 * p)
          (ProjectionCup.Constructions.projectComplement d X B K hK D hbound q (q + 2 * d) rfl c) a) := by
  rw [evenCup_swap, evenCup_swap]
  exact ProjectionCup.Constructions.projectComplement_cup d X A B hA hB K hK D hD hbound (2 * p) q a c

end AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.ProjectionRightCup

namespace AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

/-! Explicit support and degree transport for actual supported classes,
including the transports in the image-intersection and cup-swap formulas. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.ProjectionRightCup OAI.AlgebraicGeometry.CycleClass.Thom.BinarySmallSwap.Constructions

def supportDegreeTransport (X : TopCat.{0}) {A B : Set X} {n m : ℕ} (hA : A = B) (hn : n = m) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B m :=
  (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S m) hA)).hom.comp
    (eqToHom (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A k) hn)).hom

theorem supportDegreeTransport_injective (X : TopCat.{0}) {A B : Set X} {n m : ℕ}
    (hA : A = B) (hn : n = m) : Function.Injective (supportDegreeTransport X hA hn) := by
  subst B
  subst m
  exact Function.injective_id

theorem supportDegreeTransport_trans (X : TopCat.{0}) {A B C : Set X} {n m k : ℕ}
    (hA : A = B) (hB : B = C) (hn : n = m) (hm : m = k)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    supportDegreeTransport X hB hm (supportDegreeTransport X hA hn c) =
      supportDegreeTransport X (hA.trans hB) (hn.trans hm) c := by
  subst B
  subst C
  subst m
  subst k
  rfl

theorem identityMap_eq_supportCast (X : TopCat.{0}) {A B : Set X} (hA : A = B)
    (h : Set.MapsTo (𝟙 X) B A) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) h n =
      eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) hA) := by
  subst B
  exact AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) X A n

theorem supportDegreeTransport_degreeAfterSupport (X : TopCat.{0}) {A B : Set X} {n m : ℕ}
    (hA : A = B) (hn : n = m)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n) :
    supportDegreeTransport X hA hn c =
      eqToHom (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B k) hn)
        (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) hA) c) := by
  subst B
  subst m
  rfl

theorem cupSwapTransport_eq_transport (X : TopCat.{0}) (A B : Set X) (p q : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (B ∪ A) (q + p)) :
    ProjectionRightCup.cupSwapTransport X A B p q c =
      supportDegreeTransport X (Set.union_comm B A) (Nat.add_comm q p) c := by
  have h : HomologicalComplex.homologyMap (BinarySmallSwap.Constructions.unionSwap X A B) (q + p) =
      eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S (q + p)) (Set.union_comm B A)) :=
    identityMap_eq_supportCast X (Set.union_comm B A) (fun _ hx => hx.elim Or.inr Or.inl) (q + p)
  change eqToHom (congrArg (fun k => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) k)
    (Nat.add_comm q p)) (HomologicalComplex.homologyMap (BinarySmallSwap.Constructions.unionSwap X A B) (q + p) c) = _
  rw [h]
  exact (supportDegreeTransport_degreeAfterSupport X (Set.union_comm B A) (Nat.add_comm q p) c).symm

theorem imageIntersectionCup_eq_transport {M P N : Type} [TopologicalSpace N]
    (u : M → N) (v : P → N) (hu : IsOpen (Set.range u)ᶜ) (hv : IsOpen (Set.range v)ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range u)ᶜ (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (Set.range v)ᶜ (2 * q)) :
    ImageIntersectionCup.Constructions.imageIntersectionCup u v hu hv p q a b =
      supportDegreeTransport (TopCat.of N) (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u v) (Nat.mul_add 2 p q).symm
        (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of N) (Set.range u)ᶜ (Set.range v)ᶜ hu hv (2 * p) (2 * q) a b) := by
  rw [ImageIntersectionTo.Constructions.Normal.imageIntersectionCup_eq_even, Intersection.TwoSupportCup.Constructions.evenIntersectionCup_eq_twoSupport]
  rfl

theorem twoSupportCup_degreeTransport (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    {p q r s : ℕ} (hp : p = r) (hq : q = s)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q) :
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB r s
      (supportDegreeTransport X rfl hp a) (supportDegreeTransport X rfl hq b) =
    supportDegreeTransport X rfl (congrArg₂ Nat.add hp hq)
      (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup X A B hA hB p q a b) := by
  subst r
  subst s
  rfl

end AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

end

end OAI
