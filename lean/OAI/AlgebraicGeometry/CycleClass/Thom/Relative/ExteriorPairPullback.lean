import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup

/-! # Exterior Pair Pullback -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorPairPullback.Constructions

noncomputable section

/-! Pulling an exterior cup back along an actual pair of maps gives the two-support cup. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def pairMap {T X Y : TopCat.{0}} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ TopCat.of (X × Y) :=
  TopCat.ofHom ⟨fun t => (f t, g t), f.hom.continuous.prodMk g.hom.continuous⟩

theorem pairMapsTo {T X Y : TopCat.{0}} (f : T ⟶ X) (g : T ⟶ Y)
    {C D : Set T} {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f C A) (hg : Set.MapsTo g D B) :
    Set.MapsTo (pairMap f g) (C ∪ D) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) :=
  fun _ h => h.elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hg h))

theorem pair_first {T X Y : TopCat.{0}} (f : T ⟶ X) (g : T ⟶ Y)
    {C : Set T} {A : Set X} (hf : Set.MapsTo f C A) (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (pairMap f g)
      (A := C) (B := Prod.fst ⁻¹' A) (fun _ hx => hf hx) p
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodFst : TopCat.of (X × Y) ⟶ X)
        (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p a) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf p a :=
  ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (pairMap f g) (TopCat.prodFst : TopCat.of (X × Y) ⟶ X)
    (A := C) (B := Prod.fst ⁻¹' A) (C := A) (fun _ hx => hf hx) (fun _ hx => hx) p) a

theorem pair_second {T X Y : TopCat.{0}} (f : T ⟶ X) (g : T ⟶ Y)
    {D : Set T} {B : Set Y} (hg : Set.MapsTo g D B) (q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (pairMap f g)
      (A := D) (B := Prod.snd ⁻¹' B) (fun _ hx => hg hx) q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (TopCat.prodSnd : TopCat.of (X × Y) ⟶ Y)
        (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q b) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q b :=
  ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (pairMap f g) (TopCat.prodSnd : TopCat.of (X × Y) ⟶ Y)
    (A := D) (B := Prod.snd ⁻¹' B) (C := B) (fun _ hx => hg hx) (fun _ hx => hx) q) b

theorem exterior_pullback_pairMap {T X Y : TopCat.{0}} (f : T ⟶ X) (g : T ⟶ Y)
    (C D : Set T) (A : Set X) (B : Set Y)
    (hC : IsOpen C) (hD : IsOpen D) (hA : IsOpen A) (hB : IsOpen B)
    (hf : Set.MapsTo f C A) (hg : Set.MapsTo g D B) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (pairMap f g)
      (pairMapsTo f g hf hg) (p + q) (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB p q a b) =
      HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup T C D hC hD p q
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf p a)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q b) := by
  have h := HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup_naturality T C D hC hD p q (pairMap f g)
    (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' B) (hA.preimage continuous_fst) (hB.preimage continuous_snd)
    (fun _ hx => hf hx) (fun _ hx => hg hx)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodFst : TopCat.of (X × Y) ⟶ X)
      (A := Prod.fst ⁻¹' A) (B := A) (fun _ hx => hx) p a)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (TopCat.prodSnd : TopCat.of (X × Y) ⟶ Y)
      (A := Prod.snd ⁻¹' B) (B := B) (fun _ hx => hx) q b)
  rw [pair_first, pair_second] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorPairPullback.Constructions
