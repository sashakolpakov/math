import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AmbientAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedBilinearIsometry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PrescribedSubspaceTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallAction

/-! # Prescribed Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The actual reference action takes the prescribed Hodge summands at
a ball point into those at its literal arithmetic translate. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem Datum.RankThreePELDatum.referenceAmbientAction_prescribed
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s))
    (hu : Geometry.ComplexBall.PrescribedSignsB.Prescribed (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b])) P.distinguished P.compactSigns z u) :
    Geometry.ComplexBall.PrescribedSignsB.Prescribed (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b])) P.distinguished P.compactSigns
      (P.lineAction g z) (P.referenceAmbientAction g u) := by
  let H : Matrix (Fin 3) (Fin 3) E := Matrix.diagonal ![1, 1, P.b]
  let f := fun i => EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings i)
  let k := fun i => EmbeddedLinearGroup.embeddedLinearIso g (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i))
  have hH (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : Datum.RankThreePELDatum.matrixHermitian H (g x) (g y) = Datum.RankThreePELDatum.matrixHermitian H x y :=
    (Principal.BallAction.matrixHermitian_diagonal P.b (g x) (g y)).trans ((hg x y).trans (Principal.BallAction.matrixHermitian_diagonal P.b x y).symm)
  have hB (i : Fin s) (x y : Geometry.ComplexBall.PrescribedSignsB.Vec) : Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings H i (f i x) (k i y) = Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings H i x y :=
    (Geometry.ComplexBall.PrescribedSignsB.matrixB_apply _ _ _ _ _).trans ((EmbeddedBilinearIsometry.localB_embedded_isometry P.embeddings H g hH i x y).trans
      (Geometry.ComplexBall.PrescribedSignsB.matrixB_apply _ _ _ _ _).symm)
  have hl : f P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0 := P.lineAction_last_ne_zero g hg z hz
  have hw : Geometry.ComplexBall.PrescribedSignsB.lineVector (P.lineAction g z) = (f P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2)⁻¹ • f P.distinguished (Geometry.ComplexBall.PrescribedSignsB.lineVector z) :=
    NegativeLine.negativeLineCoordinate_vector _ hl
  have hh : Geometry.ComplexBall.PrescribedSignsB.Prescribed (fun i x y => Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings H i x y) P.distinguished P.compactSigns z u := by
    simpa only [Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] using hu
  have hr := PrescribedSubspaceTransport.prescribed_subspace_transport (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings H) P.distinguished P.compactSigns f k hB
    z (P.lineAction g z) _ (inv_ne_zero hl) hw u hh
  intro i
  by_cases hi : i = P.distinguished
  · simpa only [hi, ite_eq_left rfl, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, H, f, k, Datum.RankThreePELDatum.referenceAmbientAction,
      LinearEquiv.piCongrRight_apply, LinearEquiv.prodCongr_apply] using hr i
  · simpa only [ite_eq_right hi, Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, H, f, k, Datum.RankThreePELDatum.referenceAmbientAction,
      LinearEquiv.piCongrRight_apply, LinearEquiv.prodCongr_apply] using hr i

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
