import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FiberEuler

/-! # Fiber Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberEuler

noncomputable section

/-! Rational fibers compute the intrinsic Euler function, and have equal Euler characteristics over a connected locally Noetherian parameter space. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem rationalFiber_euler_eq {K : Type u} [Field K] {S X P : Scheme.{u}}
    (p : S ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ S) (hs : s ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ Spec (.of K)} {f : X ⟶ S} [IsSeparated f]
    (H : IsPullback a b f s) (L : Line.Bundles.LineBundle X) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic b (L.pullback a).sheaf =
      Geometric.FiberEuler.fiberEulerCharacteristic f L (s (IsLocalRing.closedPoint K)) := by
  let x := s (IsLocalRing.closedPoint K)
  let j := (FiberIsomorphism.rationalFiberIso p s hs H).hom
  let q := f.fiberToSpecResidueField x
  let L₀ := L.pullback (f.fiberι x)
  let M := L.pullback a
  have : IsIso j := inferInstanceAs (IsIso (FiberIsomorphism.rationalFiberIso p s hs H).hom)
  have : IsSeparated q := inferInstanceAs (IsSeparated (pullback.snd f (S.fromSpecResidueField x)))
  have : (f.fiber x).IsSeparated := ⟨by rw [← terminal.comp_from q]; infer_instance⟩
  let e := (PointResidue.rationalPointResidueIso p s hs).commRingCatIsoToRingEquiv
  have he : CohomologyEulerCharacteristic.coefficientEulerCharacteristic (b ≫ Spec.map (PointResidue.rationalPointResidueIso p s hs).hom) M.sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic b M.sheaf := HilbertConstruction.Field.CoefficientEuler.coefficientEulerCharacteristic_fieldIso e b M.sheaf
  calc
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic b M.sheaf =
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic (b ≫ Spec.map (PointResidue.rationalPointResidueIso p s hs).hom) M.sheaf := he.symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic (j ≫ q) M.sheaf :=
      congrArg (fun r => CohomologyEulerCharacteristic.coefficientEulerCharacteristic r M.sheaf) (FiberIsomorphism.rationalFiberIso_structure p s hs H).symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic (j ≫ q) (L₀.pullback j).sheaf :=
      Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso (j ≫ q) (FiberIsomorphism.rationalFiberBundleIso p s hs H L).symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic q L₀.sheaf := EulerPullbackIso.coefficientEulerCharacteristic_pullback_iso j q L₀
    _ = Geometric.FiberEuler.fiberEulerCharacteristic f L x := (FiberEulerGroundField.fiberEulerCharacteristic_eq_groundField f L x).symm

theorem connected_rationalFiber_euler_eq {K : Type u} [Field K] {S X P Q : Scheme.{u}}
    [IsLocallyNoetherian S] [PreconnectedSpace S]
    (p : S ⟶ Spec (.of K)) (s t : Spec (.of K) ⟶ S)
    (hs : s ≫ p = 𝟙 _) (ht : t ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ Spec (.of K)} {c : Q ⟶ X} {d : Q ⟶ Spec (.of K)}
    {f : X ⟶ S} [IsProper f] [Flat f]
    (Hs : IsPullback a b f s) (Ht : IsPullback c d f t) (L : Line.Bundles.LineBundle X) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic b (L.pullback a).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic d (L.pullback c).sheaf :=
  (rationalFiber_euler_eq p s hs Hs L).trans
    ((LocallyNoetherian.FiberEuler.locallyNoetherian_properFlat_fiberEuler_eq_of_preconnected f L _ _).trans
      (rationalFiber_euler_eq p t ht Ht L).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberEuler
