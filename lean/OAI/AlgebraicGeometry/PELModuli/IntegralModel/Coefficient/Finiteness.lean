import OAI.ArithmeticGeometry.Models.CoefficientSystem
import OAI.ArithmeticGeometry.Models.Scheme
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finiteness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness.Coefficients

/-! Generalization of the proved ModelFiniteness construction to a general
coefficient ring, for arithmetic parameter spaces of complex schemes.

 Finite-presentation properties of models and their morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem baseChange_finitePresentation {S T : Scheme.{u}} (f : T ⟶ S)
    (X : Over S) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism ((Over.pullback f).obj X).hom := by
  let : LocallyOfFinitePresentation X.hom := hX.1
  let : QuasiCompact X.hom := hX.2.1
  let : QuasiSeparated X.hom := hX.2.2
  change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback.snd X.hom f)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem coefficientBase_locallyNoetherian
    (R₀ K : Type u) [CommRing R₀] [Field K] [Algebra R₀ K] [IsNoetherianRing R₀] (s : Finset K) :
    IsLocallyNoetherian (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s) := by
  let : Algebra.FiniteType R₀ (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R₀ K s) :=
    ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing_finiteType R₀ K s
  let : IsNoetherianRing (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing R₀ K s) :=
    Algebra.FiniteType.isNoetherianRing R₀ _
  exact isLocallyNoetherian_Spec.mpr inferInstance

/-- A morphism between finitely presented models over a noetherian base is
itself of finite presentation. -/
theorem morphism_of_models_finitePresentation
    {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    (X Y : Over S) (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom) (f : X ⟶ Y) :
    ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism f.left := by
  let : LocallyOfFinitePresentation X.hom := hX.1
  let : LocallyOfFinitePresentation Y.hom := hY.1
  let : QuasiCompact X.hom := hX.2.1
  let : QuasiSeparated X.hom := hX.2.2
  let : QuasiSeparated Y.hom := hY.2.2
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Finiteness.Coefficients
