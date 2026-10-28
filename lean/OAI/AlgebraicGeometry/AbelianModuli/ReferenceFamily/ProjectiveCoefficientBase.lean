import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveCoefficientsId

/-! # Projective Coefficient Base -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveCoefficientBase.ProjectiveCoefficients

noncomputable section

/-! Coefficient changes commute with the actual structural morphisms
of projective space. The verification takes place on homogeneous affine
charts and their maps on constants. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R T : Type} [CommRing R] [CommRing T]

theorem awayMap_constant (f : R →+* T) (n : ℕ) (p : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing R n) (r : R) :
    HomogeneousLocalization.Away.map (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n) p
      (HomogeneousLocalization.fromZeroRingHom (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (Submonoid.powers p)
        (HilbertConstruction.Projective.ProjectivePresentations.degreeZeroConstants R n r)) =
      HomogeneousLocalization.fromZeroRingHom (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n)
        (Submonoid.powers (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n p)) (HilbertConstruction.Projective.ProjectivePresentations.degreeZeroConstants T n (f r)) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.map f (MvPolynomial.C r))
      ⟨MvPolynomial.map f 1, _⟩ = Localization.mk (MvPolynomial.C (f r)) 1
  simp only [MvPolynomial.map_C, map_one]
  rfl

theorem chart_toBase (n d : ℕ) (p : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing R n)
    (hp : p ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n d) (hd : 0 < d) :
    Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) p hp hd ≫ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).hom =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (Submonoid.powers p)).comp
          (HilbertConstruction.Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom)) := by
  change Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) p hp hd ≫
    (Proj.toSpecZero (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) ≫
      Spec.map (CommRingCat.ofHom (HilbertConstruction.Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom)) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem schemeMap_base_chart (f : R →+* T) (n d : ℕ)
    (p : HilbertConstruction.Projective.ProjectivePresentations.coordinateRing R n) (hp : p ∈ HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n d) (hd : 0 < d) :
    Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n p) ((ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n).map_mem hp) hd ≫
      (ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap f n ≫ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).hom) =
    Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n p) ((ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n).map_mem hp) hd ≫
      ((HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace T n).hom ≫ Spec.map (CommRingCat.ofHom f)) := by
  let a := Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading T n) (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n p) ((ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n).map_mem hp) hd
  let b := Proj.awayι (HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) p hp hd
  let m := Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n) p))
  have hm : a ≫ ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap f n = m ≫ b :=
    Proj.awayι_comp_map (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n) (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap_irrelevant f n) hd p hp
  have hc : m ≫ (b ≫ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).hom) =
      (a ≫ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace T n).hom) ≫ Spec.map (CommRingCat.ofHom f) := by
    rw [show b ≫ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).hom = _ from chart_toBase n d p hp hd,
      show a ≫ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace T n).hom = _ from
        chart_toBase n d (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n p) ((ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n).map_mem hp) hd]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact awayMap_constant f n p r
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).hom) hm).trans
      ((Category.assoc _ _ _).trans (hc.trans (Category.assoc _ _ _))))

theorem schemeMap_base (f : R →+* T) (n : ℕ) :
    ProjectiveCoefficientsId.ProjectiveCoefficients.schemeMap f n ≫ (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).hom =
      (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace T n).hom ≫ Spec.map (CommRingCat.ofHom f) := by
  apply (Proj.mapAffineOpenCover (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap f n) (ProjectiveCoefficientsId.ProjectiveCoefficients.gradedMap_irrelevant f n)).openCover.hom_ext
  intro a
  exact schemeMap_base_chart f n a.1.val a.2.val a.2.property a.1.property

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectiveCoefficientBase.ProjectiveCoefficients
