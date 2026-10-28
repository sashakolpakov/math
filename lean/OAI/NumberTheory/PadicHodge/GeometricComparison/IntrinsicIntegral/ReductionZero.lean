import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalDifferential
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationSectionSurjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConnectiveSectionOn
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamZero

/-! # Reduction Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionZero.IntrinsicIntegralReductionHZero

noncomputable section

/-! The actual reduction map is surjective on degree-zero derived global sections when the geometric global-function reduction is surjective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionComplex.IntrinsicIntegralReductionComplex

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

theorem zero_isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X.left)
    ((ReductionComplex.IntrinsicIntegralReductionComplex.presheafComplex R S X Y f).X 0) := by
  let F : Sheaf (Opens.grothendieckTopology Y.left) (ModuleCat S) :=
    ⟨AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S Y 0, Integral.GlobalDifferential.IntegralGlobalDifferential.zeroForms_isSheaf S Y⟩
  let G := (sheafCompose (Opens.grothendieckTopology X.left)
    (ModuleCat.restrictScalars (algebraMap R S))).obj
      ((TopCat.Sheaf.pushforward (ModuleCat S) f.base).obj F)
  exact G.property

theorem zero_unit_isIso (U : X.left.Opens) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      ((ReductionComplex.IntrinsicIntegralReductionComplex.presheafComplex R S X Y f).X 0)).app (op U)) := by
  let : IsIso (toSheafify (Opens.grothendieckTopology X.left)
      ((ReductionComplex.IntrinsicIntegralReductionComplex.presheafComplex R S X Y f).X 0)) := isIso_toSheafify _ (zero_isSheaf R S X Y f)
  infer_instance

theorem zero_sections_surjective (hf : Function.Surjective f.appTop) :
    Function.Surjective (((ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap R S X Y f h).f 0).hom.app (op ⊤)) := by
  let := zero_unit_isIso R S X Y f ⊤
  apply SheafificationSectionSurjective.SheafificationSectionSurjectivity.surjective (Opens.grothendieckTopology X.left) R
    ((ReductionComplex.IntrinsicIntegralReductionComplex.presheafMap R S X Y f h).f 0) (op ⊤)
  exact ReductionSections.IntrinsicIntegralReductionSections.surjective R S X Y f h ⊤ hf 0

def integerComplex : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) ℤ :=
  (ReductionComplex.IntrinsicIntegralReductionComplex.sheafComplex R S X Y f).extend ComplexShape.embeddingUpNat

def integerMap : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X ⟶ integerComplex R S X Y f :=
  (ComplexShape.embeddingUpNat.extendFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)).map
    (ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap R S X Y f h)

instance connective : (integerComplex R S X Y f).IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE
    ((ReductionComplex.IntrinsicIntegralReductionComplex.sheafComplex R S X Y f).extend ComplexShape.embeddingUpNat) 0
  infer_instance

theorem integer_zero_surjective (hf : Function.Surjective f.appTop) :
    Function.Surjective (((integerMap R S X Y f h).f 0).hom.app (op ⊤)) := by
  have hh := zero_sections_surjective R S X Y f h hf
  let F := (sheafSections (Opens.grothendieckTopology X.left) (ModuleCat R)).obj (op ⊤)
  let : Epi (F.map ((ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap R S X Y f h).f 0)) := (ModuleCat.epi_iff_surjective _).mpr hh
  let e₁ : (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X).X 0 ≅ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X 0 :=
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl
  let e₂ : (integerComplex R S X Y f).X 0 ≅ (ReductionComplex.IntrinsicIntegralReductionComplex.sheafComplex R S X Y f).X 0 :=
    (ReductionComplex.IntrinsicIntegralReductionComplex.sheafComplex R S X Y f).extendXIso ComplexShape.embeddingUpNat (i := 0) rfl
  have he : (integerMap R S X Y f h).f 0 = e₁.hom ≫ (ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap R S X Y f h).f 0 ≫ e₂.inv :=
    HomologicalComplex.extendMap_f (ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap R S X Y f h) ComplexShape.embeddingUpNat rfl
  apply (ModuleCat.epi_iff_surjective _).mp
  change Epi (F.map ((integerMap R S X Y f h).f 0))
  rw [he, F.map_comp, F.map_comp]
  infer_instance

theorem derived_hzero_surjective [IsIso X.hom.appTop] (hf : Function.Surjective f.appTop) :
    Function.Surjective
      (fun a : (DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) 0).obj
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X) ⟶ DerivedCategory.Q.obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplexInt R X) =>
        a ≫ DerivedCategory.Q.map (integerMap R S X Y f h)) :=
  ConnectiveSectionOn.ConnectiveSectionSurjectivity.surjective R X.left _ _ (integerMap R S X Y f h)
    (integer_zero_surjective R S X Y f h hf) (Integral.DeRhamZero.IntegralDeRhamHZero.differential_zero R X)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionZero.IntrinsicIntegralReductionHZero
