import OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator

/-! # Intrinsic Cover Topology -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicCoverTopology.Intrinsic

noncomputable section

/-! The native matrix oscillator cover is a topological group in its
specified strong L2 topology. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction

variable (k : Type) [NormedField k] (N : ℕ)

theorem symplectic_isTopologicalGroup : IsTopologicalGroup (Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply Continuous.subtype_mk
    change Continuous (fun g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N =>
      (-Matrix.J (Fin N) k) * g.val.transpose * Matrix.J (Fin N) k)
    exact (continuous_const.matrix_mul continuous_subtype_val.matrix_transpose).matrix_mul continuous_const

variable [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]

theorem localCover_isTopologicalGroup (ψ : AddChar k ℂ) : IsTopologicalGroup (Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) := by
  let : IsTopologicalGroup (Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) := symplectic_isTopologicalGroup k N
  let S := Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N
  let L := MeasureTheory.Lp ℂ 2 (Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N)
  let : NormedAddCommGroup S :=
    NormedAddCommGroup.induced S L (Weil.UnitarySplitting.Weak.Construction.testToL2 k N) (Weil.UnitarySplitting.Weak.Construction.testToL2_injective k N)
  let : NormedSpace ℂ S := NormedSpace.induced ℂ S L (Weil.UnitarySplitting.Weak.Construction.testToL2 k N)
  let p := Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ
  let r := Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ
  have hr : ∀ g, Isometry (r g) := by
    intro g
    apply AddMonoidHomClass.isometry_of_norm (r g)
    intro f
    change ‖Weil.UnitarySplitting.Weak.Construction.testToL2 k N (r g f)‖ = ‖Weil.UnitarySplitting.Weak.Construction.testToL2 k N f‖
    rw [Weil.UnitarySplitting.Weak.Construction.testToL2_norm, Weil.UnitarySplitting.Weak.Construction.testToL2_norm]
    exact congrArg Real.sqrt (g.property.1 f)
  have hdist (f h : S) : dist f h = Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N (f - h)) := by
    rw [dist_eq_norm]
    exact Weil.UnitarySplitting.Weak.Construction.testToL2_norm k N (f - h)
  have htop : Weil.AdelicSplitting.Oscillator.Construction.localCoverTopology k N ψ = Weil.UnitarySplitting.StrongTopology.operatorTopology p r := by
    unfold Weil.AdelicSplitting.Oscillator.Construction.localCoverTopology Weil.UnitarySplitting.StrongTopology.operatorTopology
    congr 1
    funext g
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext q
        exact (hdist (r g q.1) q.2).symm
      · funext q
        change Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N ((r g).symm q.1 - q.2)) = dist (r g⁻¹ q.1) q.2
        rw [map_inv, LinearEquiv.coe_inv]
        exact (hdist ((r g).symm q.1) q.2).symm
  change @IsTopologicalGroup _ (Weil.AdelicSplitting.Oscillator.Construction.localCoverTopology k N ψ) _
  rw [htop]
  exact Weil.UnitarySplitting.StrongTopology.operator_isTopologicalGroup p r hr

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicCoverTopology.Intrinsic
