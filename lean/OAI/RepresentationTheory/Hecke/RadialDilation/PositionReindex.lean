import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Position Reindex -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization

noncomputable section

section

/-! Relabeling position coordinates preserves topology and the Heisenberg formula. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

def positionReindex {I J K : Type*} [TopologicalSpace K] (e : I ≃ J) : (I → K) ≃ₜ (J → K) where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp
  continuous_toFun := continuous_pi (fun j => continuous_apply (e.symm j))
  continuous_invFun := continuous_pi (fun i => continuous_apply (e i))

theorem positionReindex_sub {I J K : Type*} [TopologicalSpace K] [Sub K]
    (e : I ≃ J) (x y : I → K) : positionReindex e (x - y) = positionReindex e x - positionReindex e y := rfl

theorem positionReindex_sum_elim {I J K : Type*} [TopologicalSpace K]
    (e : I ≃ J) (p s : I → K) :
    positionReindex (e.sumCongr e) (Sum.elim p s) = Sum.elim (positionReindex e p) (positionReindex e s) := by
  funext i
  cases i <;> rfl

theorem positionReindex_dot {I J K : Type*} [Fintype I] [Fintype J]
    [TopologicalSpace K] [CommSemiring K] (e : I ≃ J) (x y : I → K) :
    positionReindex e x ⬝ᵥ positionReindex e y = x ⬝ᵥ y := by
  exact e.symm.sum_comp (fun i => x i * y i)

theorem heisenberg_positionReindex {I J K : Type*} [Fintype I] [Fintype J]
    [TopologicalSpace K] [CommRing K] [Algebra ℚ K]
    (e : I ≃ J) (ψ : AddChar K ℂ) (p s : I → K) (f : (I → K) → ℂ) (y : J → K) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg ψ p s f ((positionReindex e).symm y) =
      Theta.PoissonAutomorphyNormalizationData.heisenberg ψ (positionReindex e p) (positionReindex e s)
        (fun z => f ((positionReindex e).symm z)) y := by
  have hsum : (∑ i, p i * (y (e i) - algebraMap ℚ K (1 / 2) * s i)) =
      ∑ j, p (e.symm j) * (y j - algebraMap ℚ K (1 / 2) * s (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using
      (e.symm.sum_comp (fun i => p i * (y (e i) - algebraMap ℚ K (1 / 2) * s i))).symm
  unfold Theta.PoissonAutomorphyNormalizationData.heisenberg
  change ψ (∑ i, p i * (y (e i) - algebraMap ℚ K (1 / 2) * s i)) *
    f (fun i => y (e i) - s i) =
    ψ (∑ j, p (e.symm j) * (y j - algebraMap ℚ K (1 / 2) * s (e.symm j))) *
      f (fun i => y (e i) - s (e.symm (e i)))
  rw [hsum]
  simp only [Equiv.symm_apply_apply]

theorem heisenberg_positionReindex_forward {I J K : Type*} [Fintype I] [Fintype J]
    [TopologicalSpace K] [CommRing K] [Algebra ℚ K]
    (e : I ≃ J) (ψ : AddChar K ℂ) (p s x : I → K) (f : (J → K) → ℂ) :
    Theta.PoissonAutomorphyNormalizationData.heisenberg ψ (positionReindex e p) (positionReindex e s) f (positionReindex e x) =
      Theta.PoissonAutomorphyNormalizationData.heisenberg ψ p s (fun y => f (positionReindex e y)) x := by
  have h := heisenberg_positionReindex e ψ p s (fun y => f (positionReindex e y)) (positionReindex e x)
  simpa only [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply] using h.symm

end

/-! Coordinate relabeling induces a symplectic group isomorphism. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [CommRing K]

theorem symplecticReindex_J (e : I ≃ J) :
    Matrix.reindexRingEquiv K (e.sumCongr e) (Matrix.J I K) = Matrix.J J K := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [Matrix.reindexRingEquiv, Matrix.reindex_apply, Matrix.J, Matrix.fromBlocks, Matrix.one_apply]

omit [DecidableEq I] [DecidableEq J] in
theorem symplecticReindex_transpose (e : I ≃ J) (A : Matrix (Sum I I) (Sum I I) K) :
    Matrix.reindexRingEquiv K (e.sumCongr e) A.transpose =
      (Matrix.reindexRingEquiv K (e.sumCongr e) A).transpose := rfl

theorem symplecticReindex_mem (e : I ≃ J) (g : Theta.PoissonAutomorphyNormalizationData.Sp I K) :
    Matrix.reindexRingEquiv K (e.sumCongr e) g.val ∈ Matrix.symplecticGroup J K := by
  have h := congrArg (Matrix.reindexRingEquiv K (e.sumCongr e)) (SymplecticGroup.mem_iff'.mp g.property)
  rw [map_mul, map_mul, symplecticReindex_transpose, symplecticReindex_J] at h
  exact SymplecticGroup.mem_iff'.mpr h

def symplecticReindex (e : I ≃ J) : Theta.PoissonAutomorphyNormalizationData.Sp I K →* Theta.PoissonAutomorphyNormalizationData.Sp J K where
  toFun g := ⟨Matrix.reindexRingEquiv K (e.sumCongr e) g.val, symplecticReindex_mem e g⟩
  map_one' := Subtype.ext (map_one (Matrix.reindexRingEquiv K (e.sumCongr e)))
  map_mul' g h := Subtype.ext (map_mul (Matrix.reindexRingEquiv K (e.sumCongr e)) g.val h.val)

theorem symplecticReindex_symm_apply (e : I ≃ J) (g : Theta.PoissonAutomorphyNormalizationData.Sp I K) :
    symplecticReindex e.symm (symplecticReindex e g) = g := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change g.val ((e.sumCongr e).symm ((e.sumCongr e) i))
    ((e.sumCongr e).symm ((e.sumCongr e) j)) = g.val i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem symplecticReindex_map {L : Type*} [CommRing L] (e : I ≃ J) (f : K →+* L) (g : Theta.PoissonAutomorphyNormalizationData.Sp I K) :
    symplecticReindex e (Theta.PoissonAutomorphyNormalizationData.mapSp f g) = Theta.PoissonAutomorphyNormalizationData.mapSp f (symplecticReindex e g) := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rfl

theorem symplecticReindex_action [TopologicalSpace K] (e : I ≃ J) (g : Theta.PoissonAutomorphyNormalizationData.Sp I K) (x : Sum I I → K) :
    (symplecticReindex e g).val *ᵥ positionReindex (e.sumCongr e) x =
      positionReindex (e.sumCongr e) (g.val *ᵥ x) := by
  have h := Matrix.submatrix_mulVec_equiv g.val (fun j => x ((e.sumCongr e).symm j))
    (e.sumCongr e).symm (e.sumCongr e).symm
  change g.val.submatrix (e.sumCongr e).symm (e.sumCongr e).symm *ᵥ
    (fun j => x ((e.sumCongr e).symm j)) = fun j => (g.val *ᵥ x) ((e.sumCongr e).symm j)
  simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using h

theorem symplecticReindex_inverse_action [TopologicalSpace K] (e : I ≃ J) (g : Theta.PoissonAutomorphyNormalizationData.Sp J K) (x : Sum I I → K) :
    positionReindex (e.sumCongr e) ((symplecticReindex e.symm g).val *ᵥ x) =
      g.val *ᵥ positionReindex (e.sumCongr e) x := by
  have h := symplecticReindex_action e (symplecticReindex e.symm g) x
  have he : symplecticReindex e (symplecticReindex e.symm g) = g :=
    symplecticReindex_symm_apply e.symm g
  rw [he] at h
  exact h.symm

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization
