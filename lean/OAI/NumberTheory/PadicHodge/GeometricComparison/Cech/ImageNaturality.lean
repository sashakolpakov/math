import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.Image
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.OpenBaseChangeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.Hypercohomology

/-! # Image Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ImageNaturality.CechImage

noncomputable section

/-! The actual Čech direct-image comparison is natural in the coefficient presheaf. -/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

theorem three_squares {C : Type*} [Category* C] {A B D E A' B' D' E' : C}
    (e₁ : A ⟶ B) (e₂ : B ⟶ D) (e₃ : D ⟶ E)
    (f₁ : A' ⟶ B') (f₂ : B' ⟶ D') (f₃ : D' ⟶ E')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D') (d : E ⟶ E')
    (h₁ : a ≫ f₁ = e₁ ≫ b) (h₂ : b ≫ f₂ = e₂ ≫ c) (h₃ : c ≫ f₃ = e₃ ≫ d) :
    a ≫ (f₁ ≫ f₂ ≫ f₃) = (e₁ ≫ e₂ ≫ e₃) ≫ d := by
  calc
    a ≫ (f₁ ≫ f₂ ≫ f₃) = e₁ ≫ (b ≫ f₂) ≫ f₃ := by
      rw [← Category.assoc a f₁ (f₂ ≫ f₃), h₁]
      simp only [Category.assoc]
    _ = e₁ ≫ (e₂ ≫ c) ≫ f₃ := by rw [h₂]
    _ = (e₁ ≫ e₂) ≫ (c ≫ f₃) := by simp only [Category.assoc]
    _ = (e₁ ≫ e₂ ≫ e₃) ≫ d := by rw [h₃]; simp only [Category.assoc]

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem coefficients_naturality {P Q : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X} (a : P ⟶ Q) :
    (IntrinsicCech.Functor.IntrinsicCechFunctor.coefficients R Y).map ((Image.CechImage.functor R f).map a) ≫ (Image.CechImage.coefficientsIso R f Q).hom =
      (Image.CechImage.coefficientsIso R f P).hom ≫ Functor.whiskerLeft (Image.CechImage.preimage f).op
        (Functor.whiskerRight ((IntrinsicCech.Functor.IntrinsicCechFunctor.coefficients R X).map a) (Image.CechImage.functor R f)) := by
  apply NatTrans.ext
  funext U
  apply NatTrans.ext
  funext V
  exact Category.comp_id _

theorem naturality {ι : Type u} (U : ι → Y.Opens)
    {P Q : AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X} (a : P ⟶ Q) :
    (IntrinsicCech.Functor.IntrinsicCechFunctor.functor R Y U).map ((Image.CechImage.functor R f).map a) ≫ (Image.CechImage.complexIso R f U Q).hom =
      (Image.CechImage.complexIso R f U P).hom ≫ ((Image.CechImage.functor R f).mapHomologicalComplex (.up ℕ)).map
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.functor R X (fun i => f ⁻¹ᵁ U i)).map a) := by
  let E := (FormalCoproduct.mk ι U).cech
  let G := (Image.CechImage.functor R f).mapHomologicalComplex (.up ℕ)
  let β := Functor.whiskerLeft (Image.CechImage.preimage f).op ((IntrinsicCech.Functor.IntrinsicCechFunctor.coefficients R X).map a)
  let eP := (cechComplexFunctor U).mapIso (Image.CechImage.coefficientsIso R f P)
  let eQ := (cechComplexFunctor U).mapIso (Image.CechImage.coefficientsIso R f Q)
  let dP := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso (Image.CechImage.functor R f) E
    ((Image.CechImage.preimage f).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P)
  let dQ := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso (Image.CechImage.functor R f) E
    ((Image.CechImage.preimage f).op ⋙ AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X Q)
  let cP := AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Image.CechImage.preimage f) U (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X P)
  let cQ := AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (Image.CechImage.preimage f) U (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.intersectionCoefficients R X Q)
  let C := cechComplexFunctor (A := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y) U
  have h₁ : C.map ((IntrinsicCech.Functor.IntrinsicCechFunctor.coefficients R Y).map ((Image.CechImage.functor R f).map a)) ≫ eQ.hom =
      eP.hom ≫ C.map (Functor.whiskerRight β (Image.CechImage.functor R f)) :=
    (C.map_comp _ _).symm.trans ((congrArg C.map (coefficients_naturality R f a)).trans (C.map_comp _ _))
  have h₂ := Section.Hypercohomology.SectionHypercohomology.inverse_square dP dQ _ _
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.naturality (Image.CechImage.functor R f) E β)
  have h₃ : G.map ((cechComplexFunctor U).map β) ≫ G.map cQ.hom =
      G.map cP.hom ≫ G.map ((IntrinsicCech.Functor.IntrinsicCechFunctor.functor R X (fun i => f ⁻¹ᵁ U i)).map a) :=
    (G.map_comp _ _).symm.trans ((congrArg G.map
      (OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.naturality (Image.CechImage.preimage f) U
        ((IntrinsicCech.Functor.IntrinsicCechFunctor.coefficients R X).map a))).trans (G.map_comp _ _))
  exact three_squares eP.hom dP.inv (G.map cP.hom) eQ.hom dQ.inv (G.map cQ.hom)
    _ _ _ _ h₁ h₂ h₃

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ImageNaturality.CechImage
