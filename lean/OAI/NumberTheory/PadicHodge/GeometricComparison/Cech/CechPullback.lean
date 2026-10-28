import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.FamilyRefinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Refinement
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ImageNaturality

/-! # Cech Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechPullback

noncomputable section

/-! Direct Čech cochains carry the actual presheaf pullback and actual cover refinement, naturally in a commuting coefficient square. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {ι κ : Type u} (U : ι → Y.Opens) (V : κ → X.Opens)
  (r : κ → ι) (hr : ∀ i, V i ≤ f ⁻¹ᵁ U (r i))

def map {P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y} {Q : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X}
    (b : P ⟶ (Image.CechImage.functor R f).obj Q) :
    (cechComplexFunctor U).obj P ⟶ (cechComplexFunctor V).obj Q :=
  (cechComplexFunctor U).map b ≫ (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Image.CechImage.preimage f) U Q).hom ≫
    FamilyRefinement.CechFamilyRefinement.map (FormalCoproduct.mk ι (fun i => f ⁻¹ᵁ U i)) (FormalCoproduct.mk κ V)
      (Refinement.CechRefinement.coverMap X (fun i => f ⁻¹ᵁ U i) V r hr) Q

theorem naturality {P P' : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y} {Q Q' : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X}
    (b : P ⟶ (Image.CechImage.functor R f).obj Q) (b' : P' ⟶ (Image.CechImage.functor R f).obj Q')
    (a : P ⟶ P') (c : Q ⟶ Q') (h : b ≫ (Image.CechImage.functor R f).map c = a ≫ b') :
    (cechComplexFunctor U).map a ≫ CechPullback.map R f U V r hr b' =
      CechPullback.map R f U V r hr b ≫ (cechComplexFunctor V).map c := by
  let T := cechComplexFunctor (A := ModuleCat.{u} R) U
  have h₁ : T.map a ≫ T.map b' = T.map b ≫ T.map ((Image.CechImage.functor R f).map c) :=
    (T.map_comp _ _).symm.trans ((congrArg T.map h.symm).trans (T.map_comp _ _))
  have h₂ := OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.naturality (Image.CechImage.preimage f) U c
  have h₃ := FamilyRefinement.CechFamilyRefinement.naturality
    (FormalCoproduct.mk ι (fun i => f ⁻¹ᵁ U i)) (FormalCoproduct.mk κ V)
    (Refinement.CechRefinement.coverMap X (fun i => f ⁻¹ᵁ U i) V r hr) c
  exact ImageNaturality.CechImage.three_squares _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechPullback
