import OAI.RepresentationTheory.Theta.Geometric.Torus.Data

/-! # Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.Transport.CM.ProjectivePeriodData

noncomputable section

/-! Linear changes of period coordinates preserve the actual projective
torus, with its quotient map and topology. -/

variable (Φ : Data.CM.ProjectivePeriodData)
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  (e : V ≃L[ℂ] Φ.space)

local instance : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V

abbrev _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.transportedLattice : Submodule ℤ V :=
  ZLattice.comap ℝ Φ.periodIntegerLattice (e.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv.toLinearMap

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.transportedLattice_map :
    (Φ.transportedLattice e).toAddSubgroup.map e.toLinearEquiv.toAddEquiv.toAddMonoidHom =
      Φ.periodIntegerLattice.toAddSubgroup := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    change e (e.symm w) ∈ Φ.periodIntegerLattice
    rw [e.apply_symm_apply]
    exact hw

def _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.transportedQuotientEquiv :
    (V ⧸ (Φ.transportedLattice e).toAddSubgroup) ≃+ Φ.periodTorus :=
  QuotientAddGroup.congr _ _ e.toLinearEquiv.toAddEquiv (Φ.transportedLattice_map e)

@[simp] theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.transportedQuotientEquiv_mk (v : V) :
    Φ.transportedQuotientEquiv e (QuotientAddGroup.mk v) = QuotientAddGroup.mk (e v) := rfl

def _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.transportedQuotientHomeomorph :
    (V ⧸ (Φ.transportedLattice e).toAddSubgroup) ≃ₜ Φ.periodTorus where
  toEquiv := (Φ.transportedQuotientEquiv e).toEquiv
  continuous_toFun := continuous_quot_lift _ (QuotientAddGroup.continuous_mk.comp e.continuous)
  continuous_invFun := continuous_quot_lift _ (QuotientAddGroup.continuous_mk.comp e.symm.continuous)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.transported_projective :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus V (Φ.transportedLattice e).toAddSubgroup := by
  obtain ⟨n, f, hf, hd⟩ := Φ.projective
  refine ⟨n, f ∘ Φ.transportedQuotientHomeomorph e,
    hf.comp (Φ.transportedQuotientHomeomorph e).isClosedEmbedding, ?_⟩
  intro v
  obtain ⟨i, hi, hdiff, hinj⟩ := hd (e v)
  refine ⟨i, hi, ?_, ?_⟩
  · exact hdiff.comp v e.differentiableAt
  · change Function.Injective (fderiv ℂ
      ((fun w => AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i
        (f (QuotientAddGroup.mk w))) ∘ e) v)
    rw [fderiv_comp v hdiff e.differentiableAt, e.fderiv]
    exact hinj.comp e.injective

def _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.transport : Data.CM.ProjectivePeriodData where
  space := V
  periodIntegerLattice := Φ.transportedLattice e
  periodIntegerLattice_discrete := inferInstance
  periodIntegerLattice_full := inferInstance
  projective := Φ.transported_projective e

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.Transport.CM.ProjectivePeriodData
