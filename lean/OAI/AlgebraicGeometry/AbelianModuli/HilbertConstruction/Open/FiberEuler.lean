import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FiberIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiberEulerGroundField

/-! # Fiber Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FiberEuler

noncomputable section

/-! The genuine fiber Euler function commutes with open base change. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem fiberEulerCharacteristic_openBaseChange
    {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    [IsSeparated f] [IsOpenImmersion g] (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) (y : Y) :
    Geometric.FiberEuler.fiberEulerCharacteristic b (L.pullback a) y = Geometric.FiberEuler.fiberEulerCharacteristic f L (g y) := by
  let j := FiberIsomorphism.baseChangeFiberMap H y
  let p := f.fiberToSpecResidueField (g y)
  let q := b.fiberToSpecResidueField y
  let L₀ := L.pullback (f.fiberι (g y))
  let M := (L.pullback a).pullback (b.fiberι y)
  have : IsIso j := inferInstanceAs (IsIso (FiberIsomorphism.openBaseChangeFiberIso H y).hom)
  have : IsSeparated p := inferInstanceAs (IsSeparated (pullback.snd f (S.fromSpecResidueField (g y))))
  have : (f.fiber (g y)).IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let e : S.residueField (g y) ≃+* Y.residueField y := (asIso (g.residueFieldMap y)).commRingCatIsoToRingEquiv
  have he : CohomologyEulerCharacteristic.coefficientEulerCharacteristic (q ≫ Spec.map (g.residueFieldMap y)) M.sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic q M.sheaf := Field.CoefficientEuler.coefficientEulerCharacteristic_fieldIso e q M.sheaf
  calc
    Geometric.FiberEuler.fiberEulerCharacteristic b (L.pullback a) y = CohomologyEulerCharacteristic.coefficientEulerCharacteristic q M.sheaf :=
      FiberEulerGroundField.fiberEulerCharacteristic_eq_groundField b (L.pullback a) y
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic (q ≫ Spec.map (g.residueFieldMap y)) M.sheaf := he.symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic (j ≫ p) M.sheaf :=
      congrArg (fun r => CohomologyEulerCharacteristic.coefficientEulerCharacteristic r M.sheaf) (FiberIsomorphism.baseChangeFiberMap_structure H y).symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic (j ≫ p) (L₀.pullback j).sheaf :=
      Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso (j ≫ p) (FiberIsomorphism.baseChangeFiberBundleIso H L y).symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L₀.sheaf := EulerPullbackIso.coefficientEulerCharacteristic_pullback_iso j p L₀
    _ = Geometric.FiberEuler.fiberEulerCharacteristic f L (g y) := (FiberEulerGroundField.fiberEulerCharacteristic_eq_groundField f L (g y)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FiberEuler
