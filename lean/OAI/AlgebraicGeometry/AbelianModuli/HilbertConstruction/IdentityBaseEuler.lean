import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EulerPullbackIso

/-! # Identity Base Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityBaseEuler

noncomputable section

/-! Pulling a line bundle through the product with the identity test scheme preserves its genuine ground-field Euler characteristic. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem coefficientEulerCharacteristic_identityBase {K : Type u} [Field K]
    {X : Scheme.{u}} [X.IsSeparated] (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (pullback.fst (𝟙 (Spec (.of K))) p)
      (L.pullback (pullback.snd (𝟙 (Spec (.of K))) p)).sheaf =
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L.sheaf := by
  let j := pullback.snd (𝟙 (Spec (.of K))) p
  have : IsIso j := inferInstanceAs (IsIso (pullback.snd (𝟙 (Spec (.of K))) p))
  have h : pullback.fst (𝟙 (Spec (.of K))) p = j ≫ p :=
    (Category.comp_id _).symm.trans pullback.condition
  exact (congrArg (fun q => CohomologyEulerCharacteristic.coefficientEulerCharacteristic q (L.pullback j).sheaf) h).trans
    (EulerPullbackIso.coefficientEulerCharacteristic_pullback_iso j p L)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IdentityBaseEuler
