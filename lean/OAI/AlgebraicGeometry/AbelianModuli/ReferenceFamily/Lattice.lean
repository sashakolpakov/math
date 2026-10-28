import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators

/-! # Lattice -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Lattice

noncomputable section

/-! The actual completed lattice is generated over the integral
finite adeles by the images of any finite integral generating set. -/

open scoped Classical

variable (E : Type*) [Field E] [Algebra ℚ E]

def finiteVectorLinear : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE (AdelicData.FiniteCoefficients E) where
  toFun := AdelicData.finiteVectorEmbedding E
  map_add' x y := funext (fun i => map_add (AdelicData.finiteCoefficientEmbedding E) (x i) (y i))
  map_smul' a x := funext (fun i => (AdelicData.finiteCoefficientEmbedding E).toLinearMap.map_smul a (x i))

variable {E} {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem completedLattice_eq_span (t : Finset (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    (ht : Submodule.span ℤ (t : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = P.lattice) :
    P.completedLattice = Submodule.span AdelicData.integralFiniteAdeles
      (AdelicData.finiteVectorEmbedding E '' (t : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))) := by
  let φ := finiteVectorLinear E
  let L := Submodule.span AdelicData.integralFiniteAdeles (φ '' (t : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)))
  have hgen (x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hx : x ∈ Submodule.span ℤ (t : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))) : φ x ∈ L := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact L.add_mem hx hy
    | smul n x _ hx =>
        rw [map_zsmul]
        have h := L.smul_mem (n : AdelicData.integralFiniteAdeles) hx
        simpa only [Int.cast_smul_eq_zsmul] using h
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact hgen x (ht.symm ▸ hx)
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, ht ▸ Submodule.subset_span hx, rfl⟩

theorem completedLattice_fg (hP : P.lattice.FG) : P.completedLattice.FG := by
  obtain ⟨t, ht⟩ := hP
  refine ⟨t.image (AdelicData.finiteVectorEmbedding E), ?_⟩
  rw [Finset.coe_image]
  exact (completedLattice_eq_span P t ht).symm

theorem integer_multiple_standard_basis_in_completedLattice
    (hP : Submodule.span ℚ (P.lattice : Set (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) = ⊤) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ j : Fin 3,
      d • (Pi.single j (1 : AdelicData.FiniteCoefficients E)) ∈ P.completedLattice := by
  obtain ⟨d, hd, hb⟩ := LatticeDenominators.common_integer_multiple_mem P.lattice hP
    (fun j : Fin 3 => Pi.single j (1 : E))
  refine ⟨d, hd, fun j => ?_⟩
  have h : finiteVectorLinear E (d • Pi.single j 1) ∈ P.completedLattice :=
    Submodule.subset_span ⟨d • Pi.single j 1, hb j, rfl⟩
  have he : finiteVectorLinear E (Pi.single j 1) = Pi.single j 1 := by
    ext i
    simp only [finiteVectorLinear, AdelicData.finiteVectorEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_apply]
    split_ifs <;> simp only [map_one, map_zero]
  rw [map_zsmul, he] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Lattice
