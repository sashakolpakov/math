import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionNormalization
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.UnitRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.GlobalRefinement

/-! # Global Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalRefinement.IntrinsicCechGlobalRefinement

noncomputable section

/-! The actual native global-section identification of Čech cochains preserves an actual cover refinement. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι κ : Type} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ U (r i)) (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)

local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl

theorem naturality :
    ((Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).mapHomologicalComplex (.up ℕ)).map
        ((Refinement.CechRefinement.sheafTransformation R X.left U V r hr).app F) ≫
      (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R X V).hom.app F =
    (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R X U).hom.app F ≫
      Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V)
        (Cech.Refinement.CechRefinement.coverMap X.left U V r hr) F.obj := by
  let E := ((evaluation X.left.Opensᵒᵖ (ModuleCat.{0} R)).obj (op ⊤)).mapHomologicalComplex (.up ℕ)
  let eU := E.mapIso (PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left U F)
  let eV := E.mapIso (PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left V F)
  let p := Cech.Refinement.CechRefinement.map R X.left U V r hr F.obj
  let q := ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).map
    ((Refinement.CechRefinement.sheafTransformation R X.left U V r hr).app F)
  have hu : E.map p ≫ eV.hom = eU.hom ≫ E.map q :=
    (E.map_comp _ _).symm.trans ((congrArg E.map
      (UnitRefinement.IntrinsicCechPresheafUnit.refinement_naturality R X.left U V r hr F)).trans (E.map_comp _ _))
  have h₁ := Section.Hypercohomology.SectionHypercohomology.inverse_square eU eV (E.map p) (E.map q) hu
  have h₂ := Cech.GlobalRefinement.CechGlobalRefinement.naturality R X U V r hr F.obj
  have h := ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂
  exact (congrArg (fun k => E.map q ≫ k) (GlobalSectionNormalization.IntrinsicCechGlobalSectionNormalization.hom R X V F)).trans
    (h.trans (congrArg (fun k => k ≫ Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι U) (FormalCoproduct.mk κ V)
      (Cech.Refinement.CechRefinement.coverMap X.left U V r hr) F.obj) (GlobalSectionNormalization.IntrinsicCechGlobalSectionNormalization.hom R X U F).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalRefinement.IntrinsicCechGlobalRefinement
