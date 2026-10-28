import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant

/-! # Slant Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantNaturality.Constructions

noncomputable section

/-! Naturality of relative slant under the actual maps of both pairs. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k]
  {X Y X' Y' : TopCat.{0}} {A : Set X} {B : Set Y} {A' : Set X'} {B' : Set Y'}

theorem slant_natural (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (p q n : ℕ) (hpq : p + q = n)
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y B q)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of k k) (TopCat.of (X' × Y'))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X' Y' A' B') n) :
    Slant.Constructions.slant k X Y A B p q n hpq b
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of k k)
          (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))
          (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg) n c) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of k k) f hf p
        (Slant.Constructions.slant k X' Y' A' B' p q n hpq
          (homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k g hg) q b) c) := by
  apply (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv k X A p).injective
  ext a
  rw [Slant.Constructions.slant_evaluation]
  have he := Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeUniversalCoefficientEquiv_naturality k
    (X := TopCat.of (X × Y)) (Y := TopCat.of (X' × Y'))
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg) n c
  refine (LinearMap.congr_fun he _).trans ?_
  refine (congrArg (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv k (TopCat.of (X' × Y'))
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X' Y' A' B') n c)
    (CrossNaturality.Constructions.relativeCrossClassAt_natural k f g hf hg p q n hpq a b)).trans ?_
  refine (Slant.Constructions.slant_evaluation k X' Y' A' B' p q n hpq _ c _).symm.trans ?_
  exact (LinearMap.congr_fun (Geometric.RelativeUniversalCoefficientNaturality.Cycles.relativeUniversalCoefficientEquiv_naturality k f hf p _) a).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SlantNaturality.Constructions
