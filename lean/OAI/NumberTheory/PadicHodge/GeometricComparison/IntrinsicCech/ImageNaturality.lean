import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Image
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ImageNaturality

/-! # Image Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ImageNaturality.IntrinsicCechImage

noncomputable section

/-! Naturality of the actual native sheaf Čech direct-image comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι : Type} (U : ι → Y.left.Opens)

theorem underlying_naturality {P Q : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X} (a : P ⟶ Q) :
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).map
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).map ((DeRham.Int.directImage f).map a)) ≫
      (Image.IntrinsicCechImage.underlyingIso f U Q).hom =
    (Image.IntrinsicCechImage.underlyingIso f U P).hom ≫
      ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).map
        (((DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)).map
          ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i)).map a)) := by
  let V := fun i => f.left ⁻¹ᵁ U i
  let G := (Cech.Image.CechImage.functor R f.left).mapHomologicalComplex (.up ℕ)
  let eP := PresheafUnit.IntrinsicCechPresheafUnit.iso R Y.left U ((DeRham.Int.directImage f).obj P)
  let eQ := PresheafUnit.IntrinsicCechPresheafUnit.iso R Y.left U ((DeRham.Int.directImage f).obj Q)
  let dP := Cech.Image.CechImage.complexIso R f.left U P.obj
  let dQ := Cech.Image.CechImage.complexIso R f.left U Q.obj
  let cP := PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left V P
  let cQ := PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left V Q
  have h₁ := Section.Hypercohomology.SectionHypercohomology.inverse_square eP eQ _ _
    (PresheafUnit.IntrinsicCechPresheafUnit.naturality R Y.left U ((DeRham.Int.directImage f).map a))
  have h₂ := Cech.ImageNaturality.CechImage.naturality R f.left U a.hom
  have h₃ : G.map ((IntrinsicCech.Functor.IntrinsicCechFunctor.functor R X.left V).map a.hom) ≫ G.map cQ.hom =
      G.map cP.hom ≫ G.map
        (((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).map
          ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left V).map a)) :=
    (G.map_comp _ _).symm.trans ((congrArg G.map (PresheafUnit.IntrinsicCechPresheafUnit.naturality R X.left V a)).trans
      (G.map_comp _ _))
  exact Cech.ImageNaturality.CechImage.three_squares eP.inv dP.hom (G.map cP.hom) eQ.inv dQ.hom (G.map cQ.hom)
    _ _ _ _ h₁ h₂ h₃

theorem map_iso_hom (P : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) :
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)).map
      (Image.IntrinsicCechImage.iso f U P).hom = (Image.IntrinsicCechImage.underlyingIso f U P).hom :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ))).map_preimage _

theorem naturality {P Q : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X} (a : P ⟶ Q) :
    (IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).map ((DeRham.Int.directImage f).map a) ≫ (Image.IntrinsicCechImage.iso f U Q).hom =
      (Image.IntrinsicCechImage.iso f U P).hom ≫ ((DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)).map
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i)).map a) := by
  let T := (sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).mapHomologicalComplex (.up ℕ)
  apply T.map_injective
  exact (T.map_comp _ _).trans
    ((congrArg (fun k => T.map ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U).map ((DeRham.Int.directImage f).map a)) ≫ k)
      (map_iso_hom f U Q)).trans
        ((underlying_naturality f U a).trans
          ((congrArg (fun k => k ≫ T.map (((DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)).map
            ((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i)).map a)))
              (map_iso_hom f U P).symm).trans (T.map_comp _ _).symm)))

def functorIso : DeRham.Int.directImage f ⋙ IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R Y.left U ≅
    IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left (fun i => f.left ⁻¹ᵁ U i) ⋙
      (DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ) :=
  NatIso.ofComponents (Image.IntrinsicCechImage.iso f U) (fun {_ _} a => naturality f U a)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ImageNaturality.IntrinsicCechImage
