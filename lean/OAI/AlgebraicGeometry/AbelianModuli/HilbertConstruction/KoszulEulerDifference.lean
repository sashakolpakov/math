import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulEulerSums
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EulerShifts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.LineBundleKoszul

/-! # Koszul Euler Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulEulerDifference

noncomputable section

/-! Finite global generators annihilate a finite tensor difference of the genuine Euler function on all line-bundle classes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem lineBundleKoszulEuler_eq_difference {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] (L M : Line.Bundles.LineBundle X)
    (ss : List (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    KoszulEulerSums.lineBundleKoszulEuler p L M.sheaf ss =
      (((LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L) - 1) ^ ss.length)
        (LineBundle.EulerShifts.lineBundleClassEuler p)) (Line.Bundles.LineBundle.classOf M) := by
  induction ss generalizing M with
  | nil =>
    rw [KoszulEulerSums.lineBundleKoszulEuler_nil]
    rfl
  | cons s ss ih =>
    have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
    have : M.sheaf.IsFiniteType := M.isFiniteType
    let e : (LineBundle.TensorEquivalence.lineBundleTensorEquivalence L).functor.obj M.sheaf ≅ (M.tensor L).sheaf :=
      LineBundle.TensorEquivalence.lineBundleTensorEquivalence_objIso L M.sheaf ≪≫ Tensor.ProductSheaf.tensorModuleCommIso L.sheaf M.sheaf
    rw [KoszulEulerSums.lineBundleKoszulEuler_cons p L M.sheaf s ss,
      KoszulEulerSums.lineBundleKoszulEuler_coefficient_iso p L e ss, ih (M.tensor L), ih M]
    rw [List.length_cons, pow_succ']
    rfl

theorem lineBundleEulerShift_difference_annihilates_of_generators
    {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p]
    (L : Line.Bundles.LineBundle X) (hL : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators L.sheaf) :
    ∃ r : ℕ, ((LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L) - 1) ^ r)
      (LineBundle.EulerShifts.lineBundleClassEuler p) = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨ss, hss⟩ := Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.exists_acyclic_koszul L hL
  refine ⟨ss.length, ?_⟩
  funext q
  induction q using Quotient.inductionOn with
  | h M =>
    have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
    have : M.sheaf.IsFiniteType := M.isFiniteType
    exact (lineBundleKoszulEuler_eq_difference p L M ss).symm.trans
      (KoszulEulerSums.lineBundleKoszulEuler_eq_zero_of_acyclic p L M.sheaf ss (hss M.sheaf).1)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KoszulEulerDifference
