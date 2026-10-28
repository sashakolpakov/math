import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationUniqueness
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidificationAt
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InterchangeNeutralFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso

/-! # Origin Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.OriginNormalization

noncomputable section

/-! An actual line isomorphism on a proper connected group product can be normalized to preserve both multiplications. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms

/-- Interchange identifies the two actual unit frames at every point neutral in both coordinates. -/
theorem unitFrames_eq {S : Scheme.{u}} {A X : Over S} [GrpObj A] [GrpObj X]
    (L : Line.Bundles.LineBundle (A ⊗ X).left)
    (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
    (hi : Compatibility.Interchange L Dh Dv)
    {T : Over S} (a : T ⟶ A ⊗ X) (hh : a ≫ fst A X = 1) (hv : a ≫ snd A X = 1) :
    Dh.unitFrame a hh = Dv.unitFrame a hv := by
  let h := InterchangeNeutralFrames.neutral_rel (snd A X) (fst A X) a hv
  exact Bilinear.ProductFrames.idempotent_frame_unique (Dv.product a a a h)
    (Dh.unitFrame a hh) (Dv.unitFrame a hv)
    (InterchangeNeutralFrames.horizontal_units_vertical_product L Dh Dv hi a a a hh hh hh h ⊤)
    (Dv.unit_left a a hv h ⊤ _)

variable {k : Type u} [Field k] (A X : Over (Spec (.of k)))
  [GrpObj A] [GrpObj X] [IsCommMonObj A] [IsCommMonObj X]
  [Smooth A.hom] [Smooth X.hom] [IsProper A.hom] [IsProper X.hom]
  [GeometricallyConnected A.hom] [GeometricallyConnected X.hom]
  (L M : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Eh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) M) (Ev : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) M)

/-- The origin fiber uniquely normalizes any existing actual line isomorphism to its prescribed unit frames. -/
theorem exists_normalized_iso (e : L.sheaf ≅ M.sheaf) :
    ∃ e' : L.sheaf ≅ M.sheaf,
      Line.FiberIsomorphisms.transportFrame L M e' (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ X)
        (Dh.unitFrame 1 (MonObj.one_comp (fst A X))) = Eh.unitFrame 1 (MonObj.one_comp (fst A X)) := by
  have : IsProper (A ⊗ X).hom := by dsimp; infer_instance
  have : Smooth (A ⊗ X).hom := by dsimp; infer_instance
  have : GeometricallyConnected (A ⊗ X).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst A.hom X.hom) A.hom
  have : ConnectedSpace (A ⊗ X).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (A ⊗ X).hom
  have : IsIntegral (A ⊗ X).left := ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral (A ⊗ X).hom
  obtain ⟨e', he', _⟩ := Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso_at_rational_point (A ⊗ X)
    (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ X).left (by simpa using (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ X).w)
    (Line.Comparison.Bundle.toShared L) (Line.Comparison.Bundle.toShared M) e
    ((Dh.unitFrame 1 (MonObj.one_comp (fst A X))).symm ≪≫ Eh.unitFrame 1 (MonObj.one_comp (fst A X)))
  refine ⟨e', ?_⟩
  exact (congrArg
    (fun z : Line.Fibers.fiber L (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ X) ≅ Line.Fibers.fiber M 1 =>
      Dh.unitFrame 1 (MonObj.one_comp (fst A X)) ≪≫ z) he').trans
        (Iso.self_symm_id_assoc _ _)

/-- Common origin units force the normalized actual line isomorphism to preserve both complete products. -/
theorem exists_productCompatible_iso (e : L.sheaf ≅ M.sheaf)
    (hL : Dh.unitFrame (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ X) (MonObj.one_comp (fst A X)) =
      Dv.unitFrame 1 (MonObj.one_comp (snd A X)))
    (hM : Eh.unitFrame (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ X) (MonObj.one_comp (fst A X)) =
      Ev.unitFrame 1 (MonObj.one_comp (snd A X))) :
    ∃ e' : L.sheaf ≅ M.sheaf,
      FiberwiseMultiplicationIso.transportMultiplication (fst A X) (snd A X) L M e' Dh = Eh ∧
      FiberwiseMultiplicationIso.transportMultiplication (snd A X) (fst A X) L M e' Dv = Ev := by
  obtain ⟨e', he'⟩ := exists_normalized_iso A X L M Dh Eh e
  refine ⟨e', AbelianScheme.IsogenyQuotient.MultiplicationUniqueness.Construction.horizontalMultiplication_eq_of_origin A X M _ Eh he', ?_⟩
  apply AbelianScheme.IsogenyQuotient.MultiplicationUniqueness.Construction.verticalMultiplication_eq_of_origin A X M
  change Line.FiberIsomorphisms.transportFrame L M e' 1 (Dv.unitFrame 1 _) = Ev.unitFrame 1 _
  rw [← hL, he', hM]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.OriginNormalization
