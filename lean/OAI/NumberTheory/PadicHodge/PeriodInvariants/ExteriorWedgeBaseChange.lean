import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorWedgeScalarNaturality

/-! # Exterior Wedge Base Change -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorWedgeBaseChange

/-! # The exterior incidence matrices commute with arbitrary scalar base change -/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul

universe u
variable {R S σ : Type u} [CommRing R] [CommRing S] [LinearOrder σ] (φ : R →+* S)

theorem basis_word_map_general {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] (b : Module.Basis σ R M) (c : Module.Basis σ S N)
    (n : ℕ) (v : Fin n → σ) (s : Set.powersetCard σ n) :
    φ ((b.exteriorPower n).repr (exteriorPower.ιMulti R n (fun k => b (v k))) s) =
      (c.exteriorPower n).repr (exteriorPower.ιMulti S n (fun k => c (v k))) s := by
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change φ (b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (b (v i))) =
    c.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (c (v i))
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

theorem basis_word_map (n : ℕ) (v : Fin n → σ) (s : Set.powersetCard σ n) :
    φ ((EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n).repr
      (exteriorPower.ιMulti R n (fun k => Finsupp.basisSingleOne (v k))) s) =
    (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n).repr
      (exteriorPower.ιMulti S n (fun k => Finsupp.basisSingleOne (v k))) s :=
  basis_word_map_general φ Finsupp.basisSingleOne Finsupp.basisSingleOne n v s

variable (R)

theorem wedge_basis_word (n : ℕ) (i : σ) (s : Set.powersetCard σ n) :
    AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n s) =
      exteriorPower.ιMulti R (n + 1) (fun k => (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R))
        ((Fin.cons i (Set.powersetCard.ofFinEmbEquiv.symm s) : Fin (n + 1) → σ) k)) := by
  let b : Module.Basis σ R (σ →₀ R) := Finsupp.basisSingleOne
  have hb : EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n s =
      exteriorPower.ιMulti R n (fun k => b (Set.powersetCard.ofFinEmbEquiv.symm s k)) :=
    exteriorPower.basis_apply R n b s
  rw [hb]
  apply (AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction.wedge_ιMulti R (σ →₀ R) (b i) n _).trans
  apply congrArg (exteriorPower.ιMulti R (n + 1))
  funext k
  exact Fin.cases rfl (fun _ => rfl) k

variable {R}

theorem wedge_matrix_map (n : ℕ) (i : σ) (s : Set.powersetCard σ n) (t : Set.powersetCard σ (n + 1)) :
    φ ((EquivariantKoszul.exteriorBasis (R := R) (σ := σ) (n + 1)).repr
      (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n s)) t) =
    (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) (n + 1)).repr
      (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge S σ i n (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n s)) t := by
  rw [wedge_basis_word, wedge_basis_word]
  exact basis_word_map φ (n + 1) (Fin.cons i (Set.powersetCard.ofFinEmbEquiv.symm s)) t

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorWedgeBaseChange
