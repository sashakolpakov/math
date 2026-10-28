import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechAcyclic
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.SectionLifting
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalAffine
import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSheafOf

/-! # Cech Section Epi -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechSectionEpi.AffineCechAcyclic

noncomputable section

/-! An affine Čech-acyclic kernel gives surjectivity on every principal-open section module of every rational affine chart. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.left) (ModuleCat R)))

theorem principal_section_epi (hS : S.ShortExact) (hA : CechAcyclic.AffineCechAcyclic.Acyclic R X S.X₁)
    (A : Type) [CommRing A] [Algebra R A] [Algebra ℚ A]
    (f : RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A ⟶ X) [IsOpenImmersion f.left] (a : A) :
    Epi (((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).map S.g).hom.app
      (op (PrimeSpectrum.basicOpen a))) := by
  have := hS.mono_f
  have := hS.epi_g
  let B := Localization.Away a
  let : Algebra R B := inferInstance
  let : Algebra ℚ B := inferInstance
  let : IsScalarTower R A B := inferInstance
  let g := PrincipalAffine.PrincipalAffineChart.map R A B
  have hg : IsOpenImmersion g.left := PrincipalAffine.PrincipalAffineChart.isOpenImmersion R A B a
  have hgf : IsOpenImmersion (g ≫ f).left := by
    change IsOpenImmersion (g.left ≫ f.left)
    infer_instance
  let G := AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R (g ≫ f).left
  let T := S.map G
  have hT : T.ShortExact := hS.map G
  have hl : Function.Surjective (T.g.hom.app (op ⊤)) :=
    SectionLifting.AffineSectionLifting.surjective R (CommRingCat.of B)
      (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R B).hom T hT
      (fun t ht => hA B (g ≫ f) t ht 0)
  have hp : Epi (T.g.hom.app (op ⊤)) := (ModuleCat.epi_iff_surjective _).mpr hl
  have hi : (g ≫ f).left ''ᵁ ⊤ = f.left ''ᵁ (PrimeSpectrum.basicOpen a) :=
    (Scheme.Hom.comp_image g.left f.left ⊤).trans
      (congrArg (fun V => f.left ''ᵁ V) (PrincipalAffine.PrincipalAffineChart.image_top R A B a))
  exact OpenSheafOf.OpenSheafSections.epi_of_chart R (g ≫ f).left
    (f.left ''ᵁ (PrimeSpectrum.basicOpen a)) hi S.g hp

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechSectionEpi.AffineCechAcyclic
