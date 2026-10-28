import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int

/-! # Open Section Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionPullback.DeRham

noncomputable section

/-! Pullback of native section algebras to an arbitrary smaller open subset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {R : Type} [CommRing R]
  {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  (U : Y.left.Opens) (V : X.left.Opens) (h : V ≤ f.left ⁻¹ᵁ U)

def sectionPullbackLE :
    letI := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y U
    letI := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X V
    Γ(Y.left, U) →ₐ[R] Γ(X.left, V) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map (homOfLE h).op).hom.comp (DeRham.Int.sectionPullback f U)

theorem sectionPullbackLE_toRingHom : (sectionPullbackLE f U V h).toRingHom = (f.left.appLE U V h).hom := rfl

def formsPullbackLE (n : ℕ) :
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R Y n).obj (op U) ⟶
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).obj (op V) :=
  ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (sectionPullbackLE f U V h)) n)

theorem formsPullbackLE_eq (n : ℕ) : formsPullbackLE f U V h n =
    (DeRham.Int.formsPullback f n).app (op U) ≫ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n).map (homOfLE h).op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_comp (CommAlgCat.ofHom (DeRham.Int.sectionPullback f U))
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map (homOfLE h).op) n ω

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionPullback.DeRham
