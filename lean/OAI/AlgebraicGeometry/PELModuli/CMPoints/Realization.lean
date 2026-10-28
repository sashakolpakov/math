import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.RealizedHodgeMaps
import Mathlib.Algebra.Module.TransferInstance

/-! # Realization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Realization

noncomputable section

/-! RiemannProjectivity produces actual CM abelian varieties: its rational H¹ comparison
transports the coefficient action and supplies a genuine CM decomposition. -/

/-- The exact realization proposition supplied by RiemannProjectivity. -/
def RiemannProjectivityInput : Prop :=
  ∀ (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E] (v : Gal(E/ℚ) → Bool)
    (hv : ∀ τ, v (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = !v τ),
    Nonempty (ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E ⟨v, hv⟩))

section Transport

variable {U V : Type*} [AddCommGroup U] [Module ℚ U]
  [AddCommGroup V] [Module ℚ V]
  (E : Type) [Field E] [Algebra ℚ E] [Module E U] [IsScalarTower ℚ E U]
  {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U}

/-- Transport a rank-one CM action along the rational comparison, while
retaining the existing additive and rational module structures. -/
theorem rankOneCMAction_transport (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) (e : U ≃ₗ[ℚ] V) :
    letI := e.symm.toAddEquiv.module E
    letI := e.symm.isScalarTower (A := E)
    ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H.transport e) := by
  let := e.symm.toAddEquiv.module E
  let := e.symm.isScalarTower (A := E)
  refine {
    numberField := h.numberField
    cmField := h.cmField
    rank_one := ?_
    hodge_action := ?_ }
  · rw [(e.symm.toAddEquiv.linearEquiv E).finrank_eq, h.rank_one]
  · intro a
    have hh := (H.transport_isHodgeMap e).comp
      ((h.hodge_action a).comp (H.transport_symm_isHodgeMap e))
    exact hh

/-- A single rank-one CM Hodge structure gives an internal one-term
decomposition on its actual underlying rational space. -/
def rankOneCMDecomposition (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) : ComplexMultiplication.Decomposition.CM.CMDecomposition H := by
  let e : U ≃ₗ[ℚ] (⊤ : Submodule ℚ U) := (Submodule.topEquiv : _ ≃ₗ[ℚ] U).symm
  letI := e.symm.toAddEquiv.module E
  letI := e.symm.isScalarTower (A := E)
  let C : ComplexMultiplication.Decomposition.CM.CMComponent H := {
    subspace := ⊤
    hodge := H.transport e
    inclusion_hodge := H.transport_symm_isHodgeMap e
    field := E
    cm := rankOneCMAction_transport E h e }
  exact {
    numberOfComponents := 1
    component := fun _ => C
    isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_subsingleton _) (by simp [C]) }

/-- CM on the realized rational H¹ is proved from the RiemannProjectivity comparison. -/
theorem realization_hasCMH1 (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) :
    R.abelianVariety.HasCMH1 := by
  let := R.comparison.symm.toAddEquiv.module E
  let := R.comparison.symm.isScalarTower (A := E)
  exact ⟨R.h1HodgeStructure, R.h1HodgeStructure_holomorphic,
    R.h1HodgeStructure_antiholomorphic,
    ⟨rankOneCMDecomposition E (rankOneCMAction_transport E h R.comparison)⟩⟩

end Transport

/-- Every odd CM sign type has an actual CM abelian realization using RiemannProjectivity. -/
theorem exists_CM_realization (hRiemannProjectivity : RiemannProjectivityInput)
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) :
    ∃ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v),
      R.abelianVariety.HasCMH1 := by
  obtain ⟨R⟩ := hRiemannProjectivity E v.val v.property
  exact ⟨R, realization_hasCMH1 E R
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction E v)⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Realization
