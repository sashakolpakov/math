import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompactPrincipalLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryLinear

/-! # Principal Open -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalOpen.Approximation

noncomputable section

/-! The original PEL principal congruence subgroup is open in its
specified finite topology, using its actual completed lattice. -/

open scoped Classical

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeTopology.TestTransport _root_.Module

variable (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

theorem pelFinite_topologicalGroup : IsTopologicalGroup P.FiniteSpecialUnitary :=
  (UnitaryLinear.Approximation.matrixPELUnitaryHomeomorph E P).symm.toHomeomorph.isInducing.isTopologicalGroup
    (UnitaryLinear.Approximation.matrixPELUnitaryHomeomorph E P).symm

theorem pelFinite_action_continuous :
    Continuous (fun p : P.FiniteSpecialUnitary × (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) => p.1.val p.2) := by
  have hm : Continuous (fun g : P.FiniteSpecialUnitary => LinearMap.toMatrix' g.val.toLinearMap) :=
    continuous_induced_dom
  exact ((hm.comp continuous_fst).matrix_mulVec continuous_snd).congr
    (fun p => LinearMap.toMatrix'_mulVec p.1.val.toLinearMap p.2)

variable {J : Type*} [Fintype J] [DecidableEq J]
  [Submodule.IsLattice ℚ P.lattice] (b : Basis J ℤ P.lattice)

include b in
theorem pelPrincipalLevel_isOpen (N : ℕ) (hN : 0 < N) :
    IsOpen (P.adelicPrincipalLevel N : Set P.FiniteSpecialUnitary) := by
  let := pelFinite_topologicalGroup E P
  have ho : IsOpen (P.completedLattice : Set (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)) :=
    LatticeTopology.TestTransport.completedVectorLattice_isOpen E P.lattice b
  have hc : IsCompact (P.completedLattice : Set (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)) :=
    LatticeTopology.TestTransport.completedVectorLattice_isCompact E P.lattice b
  have hn0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmult : IsOpen {z : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E | ∃ y ∈ P.completedLattice, z = N • y} := by
    have he : {z : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E | ∃ y ∈ P.completedLattice, z = N • y} =
        (fun y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E => (N : ℚ) • y) '' P.completedLattice := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, Nat.cast_smul_eq_nsmul ℚ N y⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, Nat.cast_smul_eq_nsmul ℚ N y⟩
    rw [he]
    exact (Homeomorph.smulOfNeZero (N : ℚ) hn0).isOpenMap _ ho
  exact CompactPrincipalLevel.Approximation.principal_lattice_comap_open
    (AbelianModuli.ReferenceFamily.Groups.specialUnitarySubgroup (R := AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) (AbelianModuli.ReferenceFamily.AdelicData.finiteHermitian E P.b)).subtype
    (pelFinite_action_continuous E P) P.completedLattice.toAddSubgroup ho hc N hmult

def pelPrincipalOpenSubgroup (N : ℕ) (hN : 0 < N) : OpenSubgroup P.FiniteSpecialUnitary :=
  ⟨P.adelicPrincipalLevel N, pelPrincipalLevel_isOpen E P b N hN⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PrincipalOpen.Approximation
