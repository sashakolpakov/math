import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PullbackAdjoint
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SectionCochainAdjoint
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechPullback

/-! # Global Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalPullback.IntrinsicCechGlobalPullback

noncomputable section

/-! The native global-section Čech comparison identifies actual geometric pullback with the direct Čech cochain pullback. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι κ : Type} (U : ι → Y.left.Opens) (V : κ → X.left.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f.left ⁻¹ᵁ U (r i))

local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of X.left)).Additive where
  map_add := rfl
local instance : (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).Additive where
  map_add := rfl

def sectionsMap (P : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) (Q : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)
    (a : (DeRham.Int.inverseImage f).obj P ⟶ Q) :
    (SectionUnit.IntrinsicCechSectionUnit.sheafSections R Y.left U).obj P ⟶
      (SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left V).obj Q :=
  Intrinsic.SectionCochainAdjoint.IntrinsicSectionCochainPullback.map f
    ((CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr).app P ≫
      (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V).map a)

theorem naturality (P : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R Y) (Q : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)
    (a : (DeRham.Int.inverseImage f).obj P ⟶ Q) :
    sectionsMap R f U V r hr P Q a ≫ (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R X V).hom.app Q =
      (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R Y U).hom.app P ≫
        Cech.CechPullback.map R f.left U V r hr ((DeRham.Int.imageAdjunction f).homEquiv P Q a).hom := by
  let c := (DeRham.Int.imageAdjunction f).homEquiv P Q a
  let T := (Section.Hypercohomology.SectionHypercohomology.sections R (TopCat.of Y.left)).mapHomologicalComplex (.up ℕ)
  let G := (DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)
  let W := fun i => f.left ⁻¹ᵁ U i
  let rQ := (Refinement.CechRefinement.sheafTransformation R X.left W V r hr).app Q
  let s₁ := T.map ((Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).map c)
  let s₂ := T.map (Image.IntrinsicCechImage.iso f U Q).hom
  let s₃ := T.map (G.map rQ)
  let e₀ := (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R Y U).hom.app P
  let e₁ := (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R Y U).hom.app ((DeRham.Int.directImage f).obj Q)
  let e₂ := (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R X W).hom.app Q
  let e₃ := (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R X V).hom.app Q
  let t₁ := (Cech.CechSheaf.functor R Y U).map c
  let t₂ := (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Cech.Image.CechImage.preimage f.left) U Q.obj).hom
  let t₃ := Cech.FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι W) (FormalCoproduct.mk κ V)
    (Cech.Refinement.CechRefinement.coverMap X.left W V r hr) Q.obj
  have h₁ : s₁ ≫ e₁ = e₀ ≫ t₁ := (GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor.iso R Y U).hom.naturality c
  have h₂ : s₂ ≫ e₂ = e₁ ≫ t₂ := GlobalImage.IntrinsicCechGlobalImage.square R f U Q
  have h₃ : s₃ ≫ e₃ = e₂ ≫ t₃ := GlobalRefinement.IntrinsicCechGlobalRefinement.naturality R X W V r hr Q
  have hm : sectionsMap R f U V r hr P Q a = s₁ ≫ s₂ ≫ s₃ :=
    (Intrinsic.SectionCochainAdjoint.IntrinsicSectionCochainPullback.map_eq_adjoint f
      ((CechPullback.IntrinsicCechPullback.refinedTransformation f U V r hr).app P ≫
        (Functor.IntrinsicCechFunctor.sheafFunctor R X.left V).map a)).trans
      ((congrArg T.map (PullbackAdjoint.IntrinsicCechPullback.adjoint_refined f U V r hr P Q a)).trans
        ((T.map_comp _ _).trans (congrArg (fun k => s₁ ≫ k) (T.map_comp _ _))))
  exact (congrArg (fun k => k ≫ e₃) hm).trans
    (Cech.ImageNaturality.CechImage.three_squares s₁ s₂ s₃ t₁ t₂ t₃ e₀ e₁ e₂ e₃ h₁.symm h₂.symm h₃.symm).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalPullback.IntrinsicCechGlobalPullback
