import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechTerms

/-! # Cech Coordinates -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechCoordinates.Construction

noncomputable section

/-! Literal coordinates of the actual infinitesimal Cech term comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R))
  {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

/-- The term isomorphism's projection is the actual chart quotient isomorphism. -/
@[reassoc]
theorem infinitesimalCechTermIso_hom_π (n q : ℕ) (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι q) :
    (CechTerms.Construction.infinitesimalCechTermIso I f U hU n q).hom ≫
      (RelativeCechTerms.Construction.relativeStructureCechTermIso (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
        (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i) q).hom ≫
      Pi.π (RelativeCechTerms.Construction.relativeCechFactor (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
        (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i) q) a =
      (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))).map
        ((RelativeCechTerms.Construction.relativeStructureCechTermIso f U q).hom ≫ Pi.π (RelativeCechTerms.Construction.relativeCechFactor f U q) a) ≫
          (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n q a).hom := by
  dsimp only [CechTerms.Construction.infinitesimalCechTermIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Pi.mapIso_hom_π,
    PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  rw [← Category.assoc, ← Functor.map_comp]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechCoordinates.Construction
