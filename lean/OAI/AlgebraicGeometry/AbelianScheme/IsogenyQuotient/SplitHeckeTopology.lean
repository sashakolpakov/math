import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CompactOpenHecke
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.Matrix

/-! # Split Hecke Topology -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeTopology.Construction

noncomputable section

/-!
The actual split integral level (product of GL3(Z_q), with one Z_q-unit
multiplier) is compact and open. Consequently every raw operator in this
split local Hecke algebra exists with the specified coefficient convention.
-/

open _root_.Topology

variable (s q : ℕ) [Fact q.Prime]

theorem integralBlockMap_openEmbedding :
    IsOpenEmbedding (Matrix.GeneralLinearGroup.map (n := Fin 3) (PadicInt.Coe.ringHom (p := q))) := by
  have hm : IsOpenEmbedding
      ((PadicInt.Coe.ringHom (p := q)).mapMatrix :
        Matrix (Fin 3) (Fin 3) ℤ_[q] →+* Matrix (Fin 3) (Fin 3) ℚ_[q]) := by
    change IsOpenEmbedding (fun m : Matrix (Fin 3) (Fin 3) ℤ_[q] =>
      fun i j => (m i j : ℚ_[q]))
    exact IsOpenEmbedding.piMap (fun _ => IsOpenEmbedding.piMap (fun _ => PadicInt.isOpenEmbedding_coe))
  exact CompactOpenHecke.Construction.units_map_openEmbedding _ hm

/-- The split integral-level map is an open embedding of topological groups. -/
theorem integralLevelMap_openEmbedding : IsOpenEmbedding (TateComparison.HeckeKernel.integralLevelMap s q) := by
  have hu : IsOpenEmbedding (Units.map (PadicInt.Coe.ringHom (p := q)).toMonoidHom) :=
    CompactOpenHecke.Construction.units_map_openEmbedding _ PadicInt.isOpenEmbedding_coe
  exact (IsOpenEmbedding.piMap (fun _ : Fin s => integralBlockMap_openEmbedding q)).prodMap hu

theorem integralLevel_isOpen : IsOpen (TateComparison.HeckeKernel.integralLevel s q : Set (TateComparison.HeckeKernel.SplitGroup s q)) :=
  (integralLevelMap_openEmbedding s q).isOpen_range

/-- Compactness follows from compact q-adic integers and the closed
embedding of a unit group into its value-and-inverse coordinates. -/
theorem integralLevel_isCompact : IsCompact (TateComparison.HeckeKernel.integralLevel s q : Set (TateComparison.HeckeKernel.SplitGroup s q)) := by
  have : CompactSpace (Matrix (Fin 3) (Fin 3) ℤ_[q]) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → ℤ_[q]))
  have : CompactSpace (Matrix.GeneralLinearGroup (Fin 3) ℤ_[q]) :=
    inferInstanceAs (CompactSpace (Matrix (Fin 3) (Fin 3) ℤ_[q])ˣ)
  exact isCompact_range (integralLevelMap_openEmbedding s q).continuous

theorem split_rawRightCosetSupport_finite (g : TateComparison.HeckeKernel.SplitGroup s q) :
    (Hecke.Construction.rawRightCosetSupport (TateComparison.HeckeKernel.integralLevel s q) g).Finite :=
  CompactOpenHecke.Construction.rawRightCosetSupport_finite_of_compact_open (TateComparison.HeckeKernel.integralLevel s q)
    (integralLevel_isOpen s q) (integralLevel_isCompact s q) g

/-- Every actual split double coset has a unique raw Hecke operator;
finite support and compact-open level geometry have been proved. -/
theorem split_raw_hecke_exists_unique (g : TateComparison.HeckeKernel.SplitGroup s q) :
    ∃! T : TateComparison.HeckeKernel.Hecke s q, TateComparison.HeckeKernel.IsRawDoubleCoset (TateComparison.HeckeKernel.integralLevel s q) g T :=
  CompactOpenHecke.Construction.compact_open_raw_hecke_exists_unique (TateComparison.HeckeKernel.integralLevel s q)
    (integralLevel_isOpen s q) (integralLevel_isCompact s q) g

/-- The concrete raw operator for the single-multiplier cocharacter. -/
def rawIntegralTypeOperator (t : TateComparison.Local.LocalType s) : TateComparison.HeckeKernel.Hecke s q :=
  Hecke.Construction.rawDoubleCosetOperator (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t)
    (split_rawRightCosetSupport_finite s q (TateComparison.HeckeKernel.representative s q t))

theorem rawIntegralTypeOperator_spec (t : TateComparison.Local.LocalType s) :
    TateComparison.HeckeKernel.IsRawDoubleCoset (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t) (rawIntegralTypeOperator s q t) :=
  Hecke.Construction.rawDoubleCosetOperator_spec (TateComparison.HeckeKernel.integralLevel s q) (TateComparison.HeckeKernel.representative s q t)
    (split_rawRightCosetSupport_finite s q (TateComparison.HeckeKernel.representative s q t))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeTopology.Construction
