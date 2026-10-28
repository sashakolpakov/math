import OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechFaceRestriction

/-! # Cech Faces -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechFaces.Construction

noncomputable section

/-! The actual infinitesimal term isomorphisms commute with every ordered Cech coface. -/

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

/-- The geometric base-change term maps intertwine the actual coface maps. -/
theorem infinitesimalCechTermIso_coface (n q : ℕ) (k : Fin (q + 2)) :
    (CechTerms.Construction.infinitesimalCechTermIso I f U hU n q).hom ≫
        RelativeCechFaces.Construction.relativeStructureCechCoface (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
          (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i) q k =
      (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))).map (RelativeCechFaces.Construction.relativeStructureCechCoface f U q k) ≫
        (CechTerms.Construction.infinitesimalCechTermIso I f U hU n (q + 1)).hom := by
  apply (cancel_mono (RelativeCechTerms.Construction.relativeStructureCechTermIso
    (pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ f)
      (fun i => pullback.fst f (Neighborhoods.Construction.infinitesimalBaseToSpec I n) ⁻¹ᵁ U i) (q + 1)).hom).mp
  apply Pi.hom_ext
  intro a
  simp only [Category.assoc]
  rw [RelativeCechFaces.Construction.relativeStructureCechCoface_π, CechCoordinates.Construction.infinitesimalCechTermIso_hom_π_assoc,
    CechCoordinates.Construction.infinitesimalCechTermIso_hom_π]
  rw [← Category.assoc _ _ (CechTerms.Construction.infinitesimalCechFactorIso I f U hU n (q + 1) a).hom,
    ← Functor.map_comp, RelativeCechFaces.Construction.relativeStructureCechCoface_π]
  simp only [Functor.map_comp, Category.assoc]
  exact congrArg (fun m =>
    (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))).map (RelativeCechTerms.Construction.relativeStructureCechTermIso f U q).hom ≫
      (AdicReduction.Construction.adicReductionFunctor (I ^ (n + 1))).map (Pi.π (RelativeCechTerms.Construction.relativeCechFactor f U q) (a.delete k)) ≫ m)
    (CechFaceRestriction.Construction.infinitesimalCechFactorIso_face I f U hU n q k a)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Infinitesimal.CechFaces.Construction
