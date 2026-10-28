import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousEndMatrixEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredMatrixUnitProjection

/-! # Filtered Operator Projection -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorProjection.Construction

noncomputable section

/-! Transport the closed filtered group and its block projection from
matrices to invertible continuous endomorphisms. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

def weightFilteredOperatorUnits {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) :
    Subgroup (L →L[ℝ] L)ˣ :=
  (FilteredMatrixUnitProjection.Construction.weightFilteredMatrixUnits w).comap (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).toMonoidHom

theorem weightFilteredOperatorUnits_isClosed {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) :
    IsClosed (weightFilteredOperatorUnits b w : Set (L →L[ℝ] L)ˣ) :=
  (FilteredMatrixUnitProjection.Construction.weightFilteredMatrixUnits_isClosed w).preimage (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).continuous

def filteredOperatorMatrixHom {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) :
    weightFilteredOperatorUnits b w →* FilteredMatrixUnitProjection.Construction.weightFilteredMatrixUnits w where
  toFun g := ⟨ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b g.val, g.property⟩
  map_one' := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).map_one
  map_mul' g h := by apply Subtype.ext; exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).map_mul g.val h.val

theorem filteredOperatorMatrixHom_continuous {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) :
    Continuous (filteredOperatorMatrixHom b w) :=
  ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).continuous.comp continuous_subtype_val).subtype_mk _

def weightBlockOperatorUnitProjection {m : ℕ} (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) :
    weightFilteredOperatorUnits b w →* (L →L[ℝ] L)ˣ :=
  (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).symm.toMonoidHom.comp
    ((FilteredMatrixUnitProjection.Construction.weightBlockUnitProjection w).comp (filteredOperatorMatrixHom b w))

theorem weightBlockOperatorUnitProjection_continuous {m : ℕ}
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) : Continuous (weightBlockOperatorUnitProjection b w) :=
  (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).symm.continuous.comp
    ((FilteredMatrixUnitProjection.Construction.weightBlockUnitProjection_continuous w).comp (filteredOperatorMatrixHom_continuous b w))

theorem weightBlockOperatorUnitProjection_matrix {m : ℕ}
    (b : Module.Basis (Fin m) ℝ L) (w : Fin m → ℝ) (g : weightFilteredOperatorUnits b w) :
    ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b (weightBlockOperatorUnitProjection b w g : L →L[ℝ] L) =
      Weight.BlockProjection.Construction.weightBlockProjection w (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b (g.val : L →L[ℝ] L)) := by
  have he := (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b).apply_symm_apply
    (FilteredMatrixUnitProjection.Construction.weightBlockUnitProjection w (filteredOperatorMatrixHom b w g))
  exact congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ => (u : Matrix (Fin m) (Fin m) ℝ)) he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorProjection.Construction
