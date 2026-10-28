import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleEuler

/-! # Euler Pullback Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EulerPullbackIso

noncomputable section

/-! Genuine line-bundle Euler characteristics are invariant under scheme isomorphisms over the coefficient field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem coefficientEulerCharacteristic_pullback_iso
    {K : Type u} [Field K] {X Y : Scheme.{u}} [Y.IsSeparated]
    (f : X ⟶ Y) [IsIso f] (p : Y ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle Y) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (f ≫ p) (L.pullback f).sheaf = CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L.sheaf := by
  apply finsum_congr
  intro q
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ)) (CohomologyPullbackIso.lineBundleCohomologyPullbackIso f p L q).toLinearEquiv.finrank_eq

theorem coefficientEulerCharacteristic_overIso
    {K : Type u} [Field K] {A B : Over (Spec (.of K))} [B.left.IsSeparated]
    (e : A ≅ B) (L : Line.Bundles.LineBundle B.left) (M : Line.Bundles.LineBundle A.left)
    (h : (L.pullback e.hom.left).sheaf ≅ M.sheaf) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.hom M.sheaf = CohomologyEulerCharacteristic.coefficientEulerCharacteristic B.hom L.sheaf := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map e.hom))
  calc
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.hom M.sheaf =
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.hom (L.pullback e.hom.left).sheaf :=
      Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso A.hom h.symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic (e.hom.left ≫ B.hom) (L.pullback e.hom.left).sheaf :=
      congrArg (fun p => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.pullback e.hom.left).sheaf) e.hom.w.symm
    _ = CohomologyEulerCharacteristic.coefficientEulerCharacteristic B.hom L.sheaf :=
      coefficientEulerCharacteristic_pullback_iso e.hom.left B.hom L

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EulerPullbackIso
