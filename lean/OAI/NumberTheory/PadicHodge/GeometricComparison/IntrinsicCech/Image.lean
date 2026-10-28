import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Image
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PresheafUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int

/-! # Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Image.IntrinsicCechImage

noncomputable section

/-! The actual native sheaf Čech resolution commutes with direct image and inverse-image covering opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι : Type} (U : ι → Y.left.Opens)

def underlyingIso (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) :
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).obj
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).obj ((DeRham.Int.directImage f).obj F)) ≅
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).obj
      (((DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)).obj
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i)).obj F)) :=
  (PresheafUnit.IntrinsicCechPresheafUnit.iso R Y.left U ((DeRham.Int.directImage f).obj F)).symm ≪≫
    Cech.Image.CechImage.complexIso R f.left U F.obj ≪≫
      ((Cech.Image.CechImage.functor R f.left).mapHomologicalComplex (.up ℕ)).mapIso
        (PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left (fun i => f.left ⁻¹ᵁ U i) F)

def iso (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) :
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).obj ((DeRham.Int.directImage f).obj F) ≅
      ((DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)).obj
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i)).obj F) :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ))).preimageIso
      (underlyingIso f U F)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Image.IntrinsicCechImage
