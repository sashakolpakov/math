import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableFine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformAuxiliaryParameters
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.FineBaseChange

/-! # Concrete Auxiliary Pure Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConcreteAuxiliaryPureModel

noncomputable section

/-! One actual auxiliary pure fine model for the original admissible
PEL datum. All numerical bounds and the Hilbert rank profile are proved
from the datum and its genuine reference fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_actual_auxiliary_pure_model
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (hs : 0 < s)
    (K : Type) [Field K] [CharZero K] :
    ∃ N : ℕ, 3 ≤ N ∧ ∃ M : Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType N (Spec (.of K)),
      Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space) ∧ M.IsFine := by
  have hδ : ∀ i, 0 < P.polarizationType i := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
    exact hpos
  let g := 3 * s
  let δ := P.polarizationType
  let N := UniformAuxiliaryParameters.uniformAuxiliaryLevel g δ
  let D := UniformAuxiliaryParameters.uniformRelationDegree g δ
  let : NeZero N := ⟨UniformAuxiliaryParameters.uniformAuxiliaryLevel_ne_zero g δ⟩
  have hN : 3 ≤ N := UniformAuxiliaryParameters.uniformAuxiliaryLevel_three_le g δ
  have hH := UniformAuxiliaryParameters.uniformAuxiliaryParameters_rankProfile P hP hs
  have hD := UniformAuxiliaryParameters.uniformHilbertFamilyDegree_le_relationDegree g δ
  let M := UniformStableModel.uniformStableModel g δ hδ N hN D hH hD
  let Q := UniformStableModel.uniformStableModel_quasiProjective g δ hδ N hN D hH hD
  have hM : M.IsFine := UniformStableFine.uniformStableModel_isFine g δ hδ N hN D hH hD
    (Nat.mul_pos (by decide) hs) (UniformAuxiliaryParameters.uniformRelationDegree_pos g δ)
    (UniformAuxiliaryParameters.uniformAuxiliaryLevel_frame_bound g δ) (UniformAuxiliaryParameters.uniformAuxiliaryLevel_detection_bound g δ)
  let f : Spec (.of K) ⟶ Spec (.of ℚ) := Spec.map (CommRingCat.ofHom (algebraMap ℚ K))
  exact ⟨N, hN, M.pullback f, ⟨Q.baseChange f⟩, hM.pullback f⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConcreteAuxiliaryPureModel
