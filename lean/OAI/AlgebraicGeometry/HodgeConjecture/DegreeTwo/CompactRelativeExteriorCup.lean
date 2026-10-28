import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactExteriorCup

/-! # Compact Relative Exterior Cup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactRelativeExteriorCup.Constructions

noncomputable section

/-! The actual compact-relative exterior cup and its pair-map naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false

theorem relativePairCohomology_supportCast {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A A' : Set X} {B B' : Set Y} (hA : A = A') (hB : B = B')
    (hm : Set.MapsTo f A B) (hm' : Set.MapsTo f A' B') (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hm' n
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y S n) hB) a) =
    eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) hA)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hm n a) := by
  subst A' B'
  rfl

def compactRelativeExteriorCup (X Y : TopCat.{0}) [T2Space X] [T2Space Y]
    (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y))
      ((K ×ˢ L : Compacts (X×Y)) : Set (X×Y))ᶜ (p+q) :=
  eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (X×Y)) S (p+q)) (CompactExteriorCup.Constructions.compactProductComplement X Y K L))
    (ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y (K : Set X)ᶜ (L : Set Y)ᶜ
      K.isCompact.isClosed.isOpen_compl L.isCompact.isClosed.isOpen_compl p q a b)

theorem compactRelativeExteriorCup_ι (X Y : TopCat.{0}) [T2Space X] [T2Space Y]
    (K : Compacts X) (L : Compacts Y) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K : Set X)ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y (L : Set Y)ᶜ q) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (X×Y)) (K×ˢL) (p+q)
      (compactRelativeExteriorCup X Y K L p q a b) = CompactExteriorCup.Constructions.compactExteriorCupStage X Y K L p q a b := rfl

variable {X X' Y Y' : TopCat.{0}} [T2Space X] [T2Space X'] [T2Space Y] [T2Space Y']

theorem compactRelativeExteriorCup_naturality (f : X ⟶ X') (g : Y ⟶ Y')
    (K : Compacts X) (K' : Compacts X') (L : Compacts Y) (L' : Compacts Y')
    (hf : Set.MapsTo f (K : Set X)ᶜ (K' : Set X')ᶜ)
    (hg : Set.MapsTo g (L : Set Y)ᶜ (L' : Set Y')ᶜ)
    (hfg : Set.MapsTo (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
      ((K ×ˢ L : Compacts (X×Y)) : Set (X×Y))ᶜ
      ((K' ×ˢ L' : Compacts (X'×Y')) : Set (X'×Y'))ᶜ) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X' (K' : Set X')ᶜ p)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y' (L' : Set Y')ᶜ q) :
    compactRelativeExteriorCup X Y K L p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf p a)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg q b) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y'))) hfg (p+q)
      (compactRelativeExteriorCup X' Y' K' L' p q a b) := by
  unfold compactRelativeExteriorCup
  rw [ExteriorCupNaturality.Constructions.relativeExteriorCup_naturality f g hf hg]
  exact (relativePairCohomology_supportCast
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
    (CompactExteriorCup.Constructions.compactProductComplement X Y K L) (CompactExteriorCup.Constructions.compactProductComplement X' Y' K' L')
    (RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg) hfg (p+q) _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactRelativeExteriorCup.Constructions
