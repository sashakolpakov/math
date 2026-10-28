import OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul

/-! # Exterior Wedge Scalar Naturality -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorWedgeScalarNaturality

/-! # The exterior-wedge incidence matrices are fixed by every scalar endomorphism -/

open _root_.Module OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul

universe u
variable {R M I : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [LinearOrder I] (φ : R →+* R) (b : Module.Basis I R M)

theorem basis_word_fixed (n : ℕ) (v : Fin n → I) (s : Set.powersetCard I n) :
    φ ((b.exteriorPower n).repr (exteriorPower.ιMulti R n (fun k => b (v k))) s) =
      (b.exteriorPower n).repr (exteriorPower.ιMulti R n (fun k => b (v k))) s := by
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change φ (b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (b (v i))) =
    b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (b (v i))
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

variable {σ : Type u} [LinearOrder σ]

theorem wedge_matrix_fixed (n : ℕ) (i : σ) (s : Set.powersetCard σ n) (t : Set.powersetCard σ (n + 1)) :
    φ ((EquivariantKoszul.exteriorBasis (R := R) (σ := σ) (n + 1)).repr
      (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n s)) t) =
    (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) (n + 1)).repr
      (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n s)) t := by
  let b : Module.Basis σ R (σ →₀ R) := Finsupp.basisSingleOne
  let v : Fin (n + 1) → σ := Fin.cons i (Set.powersetCard.ofFinEmbEquiv.symm s)
  have hb : EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n s =
      exteriorPower.ιMulti R n (fun k => b (Set.powersetCard.ofFinEmbEquiv.symm s k)) :=
    exteriorPower.basis_apply R n b s
  have hw : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n s) =
      exteriorPower.ιMulti R (n + 1) (fun k => b (v k)) := by
    rw [hb]
    apply (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge_ιMulti R (σ →₀ R) (b i) n _).trans
    apply congrArg (exteriorPower.ιMulti R (n + 1))
    funext k
    exact Fin.cases rfl (fun _ => rfl) k
  rw [hw]
  exact basis_word_fixed φ b (n + 1) v t

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorWedgeScalarNaturality
