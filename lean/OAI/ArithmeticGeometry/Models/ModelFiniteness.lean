import OAI.ArithmeticGeometry.Models.CoefficientSystem
import OAI.ArithmeticGeometry.Models.Scheme
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Model Finiteness -/

namespace OAI.ArithmeticGeometry.Models.ModelFiniteness.Constructions.Foundations

/-! Finite-presentation properties of models and their morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem baseChange_finitePresentation {S T : Scheme.{u}} (f : T ⟶ S)
    (X : Over S) (hX : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) :
    Models.Scheme.Constructions.Foundations.FinitePresentationMorphism ((Over.pullback f).obj X).hom := by
  let : LocallyOfFinitePresentation X.hom := hX.1
  let : QuasiCompact X.hom := hX.2.1
  let : QuasiSeparated X.hom := hX.2.2
  change Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (pullback.snd X.hom f)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem coefficientBase_locallyNoetherian
    (K : Type u) [Field K] [NumberField K] (s : Finset K) :
    IsLocallyNoetherian (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s) := by
  let : Algebra.FiniteType (𝓞 K) (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) :=
    CoefficientSystem.Constructions.Foundations.coefficientRing_finiteType (𝓞 K) K s
  let : IsNoetherianRing (CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s) :=
    Algebra.FiniteType.isNoetherianRing (𝓞 K) _
  exact isLocallyNoetherian_Spec.mpr inferInstance

/-- A morphism between finitely presented models over a noetherian base is
itself of finite presentation. -/
theorem morphism_of_models_finitePresentation
    {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
    (X Y : Over S) (hX : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (hY : Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom) (f : X ⟶ Y) :
    Models.Scheme.Constructions.Foundations.FinitePresentationMorphism f.left := by
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

end OAI.ArithmeticGeometry.Models.ModelFiniteness.Constructions.Foundations
