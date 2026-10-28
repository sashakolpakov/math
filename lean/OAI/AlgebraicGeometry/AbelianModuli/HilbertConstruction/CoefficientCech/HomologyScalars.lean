import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyForget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PresheafScalarAction
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Homology Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyScalars

noncomputable section

/-! Coefficient scalars act on native Čech homology by the genuine linear action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem cochainHomologyMap_smul {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (r : R) (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (r • f) n = r • HomologicalComplex.homologyMap f n := by
  change ShortComplex.homologyMap
    (r • (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map f) = _
  exact ShortComplex.homologyMap_smul (R := R) (C := ModuleCat.{u} R)
    (S₁ := K.sc n) (S₂ := L.sc n)
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map f) r

theorem coefficientCech_globalScalar_map {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (r : R) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map (Global.ModuleScalars.globalModuleScalar M (c r)) =
      r • 𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U) := by
  apply ScalarMaps.coefficientCechComplexFunctor_map_eq_smul_id
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem coefficientCech_globalScalar_homologyMap {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (r : R) (n : ℕ) :
    HomologicalComplex.homologyMap
      ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map (Global.ModuleScalars.globalModuleScalar M (c r))) n =
        r • 𝟙 ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).homology n) := by
  exact (congrArg (fun f : Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U ⟶ Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U =>
    HomologicalComplex.homologyMap f n) (coefficientCech_globalScalar_map c M U r)).trans
      ((cochainHomologyMap_smul r (𝟙 (Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U)) n).trans
        (congrArg (fun f => r • f)
          (HomologicalComplex.homologyMap_id (Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U) n)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyScalars
