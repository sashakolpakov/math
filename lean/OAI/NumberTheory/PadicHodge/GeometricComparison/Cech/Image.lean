import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Lattice

/-! # Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Image.CechImage

noncomputable section

/-! Actual direct image of presheaves carries the Čech complex on inverse-image opens to the original Čech complex. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)

def preimage : Y.Opens ⥤ X.Opens := TopologicalSpace.Opens.map f.base

instance preimage_preservesFiniteLimits : PreservesFiniteLimits (preimage f) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
  infer_instance

def functor : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X ⥤ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y :=
  (Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ (ModuleCat.{u} R)).obj (preimage f).op

instance additive : (functor R f).Additive := by
  dsimp only [functor]
  infer_instance

instance preservesLimits : PreservesLimitsOfSize.{u, u} (functor R f) := by
  dsimp only [functor]
  infer_instance

def coefficientsIso (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R Y ((functor R f).obj P) ≅
      (preimage f).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P ⋙ functor R f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V a
    apply NatTrans.ext
    funext W
    rfl)

def complexIso {ι : Type u} (U : ι → Y.Opens) (P : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X) :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R Y U ((functor R f).obj P) ≅
      ((functor R f).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.complex R X (fun i => f ⁻¹ᵁ U i) P) :=
  (cechComplexFunctor U).mapIso (coefficientsIso R f P) ≪≫
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso (functor R f) (FormalCoproduct.mk ι U).cech
      ((preimage f).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P)).symm ≪≫
        ((functor R f).mapHomologicalComplex (.up ℕ)).mapIso
          (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (preimage f) U (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Image.CechImage
