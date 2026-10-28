import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Local Norm Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalNormSections.Construction

noncomputable section

/-! Actual local norm sections on affine opens of a finite morphism.
Their input is the original global section, transported through the
canonical restriction square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.NonvanishingBaseChange

universe u
variable {X Y : Scheme.{u}} (q : X ⟶ Y) [IsFinite q] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (d : ℕ)

structure NormFrameOpen where
  openSet : Y.Opens
  affine : IsAffineOpen openSet
  basis : letI := (q ∣_ openSet).appTop.hom.toAlgebra
    Module.Basis (Fin d) Γ(openSet.toScheme, ⊤) Γ((q ⁻¹ᵁ openSet).toScheme, ⊤)
  frame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule openSet.toScheme ≅ (L.pullback openSet.ι).sheaf

variable {q L d}

def localNormInput (U : Y.Opens)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (q ⁻¹ᵁ U).toScheme ⟶ ((L.pullback U.ι).pullback (q ∣_ U)).sheaf :=
  AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (q ⁻¹ᵁ U).ι z ≫
    (PullbackSectionSquares.Construction.sectionPullbackSquareIso q (q ∣_ U) (q ⁻¹ᵁ U).ι U.ι
      (morphismRestrict_ι q U).symm L.sheaf).hom

def localNormSection (U : NormFrameOpen q L d)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.openSet.toScheme ⟶ ((L.tensorPower d).pullback U.openSet.ι).sheaf :=
  FramedNormSection.Construction.framedNormSection (q ∣_ U.openSet) U.frame.hom d (localNormInput U.openSet z) ≫
    (L.powerBaseChangeIso U.openSet.ι d).inv

omit [IsFinite q] in
theorem localNormInput_nonvanishing (U : Y.Opens)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (localNormInput U z) = (q ⁻¹ᵁ U).ι ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z :=
  (AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (q ⁻¹ᵁ U).ι z)
    (PullbackSectionSquares.Construction.sectionPullbackSquareIso q (q ∣_ U) (q ⁻¹ᵁ U).ι U.ι
      (morphismRestrict_ι q U).symm L.sheaf)).trans
    (AbelianModuli.HilbertConstruction.Section.Nonvanishing.sectionNonvanishing_pullback (q ⁻¹ᵁ U).ι z)

set_option backward.isDefEq.respectTransparency false in
theorem localNormSection_mem_nonvanishing (U : NormFrameOpen q L d)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (L.pullback q).sheaf) (y : U.openSet.toScheme) :
    y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (localNormSection U z) ↔
      ∀ x : X, q x = U.openSet.ι y → x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z := by
  have : IsAffine U.openSet.toScheme := U.affine
  have : IsAffine (q ⁻¹ᵁ U.openSet).toScheme := isAffine_of_isAffineHom (q ∣_ U.openSet)
  have hD : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (localNormSection U z) =
      AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (FramedNormSection.Construction.framedNormSection (q ∣_ U.openSet) U.frame.hom d (localNormInput U.openSet z)) :=
    AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso _ (L.powerBaseChangeIso U.openSet.ι d).symm
  rw [hD, FramedNormSection.Construction.framedNormSection_mem_nonvanishing (q ∣_ U.openSet) U.basis,
    localNormInput_nonvanishing]
  constructor
  · intro h x hx
    have hxU : x ∈ q ⁻¹ᵁ U.openSet :=
      (congrArg (fun y : Y => y ∈ U.openSet) hx).mpr y.property
    have hy : (q ∣_ U.openSet) (⟨x, hxU⟩ : (q ⁻¹ᵁ U.openSet).toScheme) = y := by
      apply U.openSet.ι.isOpenEmbedding.injective
      exact (congrArg (fun f => f (⟨x, hxU⟩ : (q ⁻¹ᵁ U.openSet).toScheme))
        (morphismRestrict_ι q U.openSet)).trans hx
    exact h ⟨x, hxU⟩ hy
  · intro h x hx
    exact h x.val ((congrArg (fun f => f x) (morphismRestrict_ι q U.openSet)).symm.trans
      (congrArg U.openSet.ι hx))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LocalNormSections.Construction
