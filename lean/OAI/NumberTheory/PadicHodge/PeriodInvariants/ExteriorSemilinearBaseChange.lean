import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorWedgeBaseChange

/-! # Exterior Semilinear Base Change -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorSemilinearBaseChange

noncomputable section

/-! # Actual semilinear base change of free exterior modules and their wedge maps -/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.EquivariantKoszul

universe u
variable {R S σ : Type u} [CommRing R] [CommRing S] [LinearOrder σ] (φ : R →+* S)

def scalarMap : R →ₛₗ[φ] S where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_mul φ

def exteriorMap (n : ℕ) : (⋀[R]^n (σ →₀ R)) →ₛₗ[φ] (⋀[S]^n (σ →₀ S)) :=
  (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n).repr.symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (scalarMap φ)).comp (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n).repr.toLinearMap)

theorem exteriorMap_repr (n : ℕ) (x : ⋀[R]^n (σ →₀ R)) (s : Set.powersetCard σ n) :
    (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n).repr (exteriorMap φ n x) s =
      φ ((EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n).repr x s) :=
  congrArg (fun f : Set.powersetCard σ n →₀ S => f s)
    ((EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n).repr.apply_symm_apply
      (Finsupp.mapRange.linearMap (scalarMap φ) ((EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n).repr x)))

theorem exteriorMap_basis (n : ℕ) (s : Set.powersetCard σ n) :
    exteriorMap φ n (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n s) = EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n s := by
  apply (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) n).repr.injective
  apply Finsupp.ext
  intro t
  rw [exteriorMap_repr, Module.Basis.repr_self, Module.Basis.repr_self]
  simp only [Finsupp.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

theorem wedge_commutes (n : ℕ) (i : σ) (x : ⋀[R]^n (σ →₀ R)) :
    exteriorMap φ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n x) =
      AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge S σ i n (exteriorMap φ n x) := by
  have he : (exteriorMap φ (n + 1)).comp (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n) =
      (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge S σ i n).comp (exteriorMap φ n) := by
    apply (EquivariantKoszul.exteriorBasis (R := R) (σ := σ) n).ext
    intro s
    change exteriorMap φ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n (EquivariantKoszul.exteriorBasis n s)) = _
    apply (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) (n + 1)).repr.injective
    apply Finsupp.ext
    intro t
    change (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) (n + 1)).repr
      (exteriorMap φ (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge R σ i n (EquivariantKoszul.exteriorBasis n s))) t =
        (EquivariantKoszul.exteriorBasis (R := S) (σ := σ) (n + 1)).repr
          (AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.exteriorWedge S σ i n (exteriorMap φ n (EquivariantKoszul.exteriorBasis n s))) t
    rw [exteriorMap_repr, exteriorMap_basis]
    exact ExteriorWedgeBaseChange.wedge_matrix_map φ n i s t
  exact LinearMap.congr_fun he x

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ExteriorSemilinearBaseChange
