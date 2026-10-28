import OAI.LinearAlgebra.Symplectic.BigCell
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Generators -/

namespace OAI.RepresentationTheory.Theta.Generators.PoissonAutomorphyConstruction

noncomputable section

/-! Algebraic reductions of rational theta invariance. No Poisson or theta
identity is added to the representation data. -/

open scoped _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def upper (B : Matrix ι ι ℚ) (hB : B.IsSymm) : PoissonAutomorphyNormalizationData.Sp ι ℚ := by
  refine ⟨Matrix.fromBlocks 1 B 0 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hB.eq]

def levi (A : (Matrix ι ι ℚ)ˣ) : PoissonAutomorphyNormalizationData.Sp ι ℚ := by
  refine ⟨Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [← Matrix.transpose_mul]

def weyl (ι : Type*) [Fintype ι] [DecidableEq ι] : PoissonAutomorphyNormalizationData.Sp ι ℚ := by
  refine ⟨Matrix.fromBlocks 0 (-1) 1 0, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp

def lower (B : Matrix ι ι ℚ) (hB : B.IsSymm) : PoissonAutomorphyNormalizationData.Sp ι ℚ := by
  refine ⟨Matrix.fromBlocks 1 0 B 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hB.eq]

theorem lower_conjugation (B : Matrix ι ι ℚ) (hB : B.IsSymm) :
    lower B hB = weyl ι * upper (-B) hB.neg * (weyl ι)⁻¹ := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 0 B 1 =
    (weyl ι).val * (upper (-B) hB.neg).val * ((weyl ι)⁻¹).val
  rw [SymplecticGroup.coe_inv]
  simp [weyl, upper, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

/-- Reuses mathlib's proved big-cell lemma, which is private in the pinned
mathlib version. This name refers to its kernel-checked proof, not an axiom. -/
theorem exists_upper_bigCell (g : PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    ∃ (B : Matrix ι ι ℚ) (hB : B.IsSymm),
      IsUnit ((upper B hB * g).val.toBlocks₁₁).det := by
  have hex : ∃ B : Matrix ι ι ℚ, B.IsSymm ∧
      IsUnit (g.val.toBlocks₁₁ + B * g.val.toBlocks₂₁).det := by
    apply LinearAlgebra.Symplectic.BigCell.SymplecticBigCell.exists_symmetric_X_isUnit_det_add_mul_of_symplectic
    exact (show Matrix.fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂
      g.val.toBlocks₂₁ g.val.toBlocks₂₂ ∈ Matrix.symplecticGroup ι ℚ from by
        simpa only [Matrix.fromBlocks_toBlocks] using g.property)
  obtain ⟨B, hB, hdet⟩ := hex
  refine ⟨B, hB, ?_⟩
  change IsUnit (((upper B hB).val * g.val).toBlocks₁₁).det
  rw [← Matrix.fromBlocks_toBlocks g.val]
  simpa [upper, Matrix.fromBlocks_multiply] using hdet

theorem bigCell_parameters_symmetric (A : (Matrix ι ι ℚ)ˣ)
    (B C D : Matrix ι ι ℚ)
    (hg : Matrix.fromBlocks A.val B C D ∈ Matrix.symplecticGroup ι ℚ) :
    (C * (A⁻¹).val).IsSymm ∧ ((A⁻¹).val * B).IsSymm := by
  have hac := (SymplecticGroup.fromBlocks_mem_iff.mp hg).1
  have hab := (SymplecticGroup.fromBlocks_mem_iff.mp
    (show Matrix.fromBlocks A.val.transpose C.transpose B.transpose D.transpose ∈
      Matrix.symplecticGroup ι ℚ from by
        simpa only [Matrix.fromBlocks_transpose] using SymplecticGroup.transpose_mem hg)).1
  simp only [Matrix.transpose_transpose] at hab
  constructor
  · change (C * (A⁻¹).val).transpose = C * (A⁻¹).val
    have h := congrArg (fun M => (A⁻¹).val.transpose * M * (A⁻¹).val) hac
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.transpose_one, one_mul] at h
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one] using h.symm
  · change ((A⁻¹).val * B).transpose = (A⁻¹).val * B
    have h := congrArg (fun M => (A⁻¹).val * M * (A⁻¹).val.transpose) hab
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul] at h
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
      mul_one] using h

theorem bigCell_factorization (A : (Matrix ι ι ℚ)ˣ)
    (B C D : Matrix ι ι ℚ)
    (hg : Matrix.fromBlocks A.val B C D ∈ Matrix.symplecticGroup ι ℚ) :
    (⟨Matrix.fromBlocks A.val B C D, hg⟩ : PoissonAutomorphyNormalizationData.Sp ι ℚ) =
      lower (C * (A⁻¹).val) (bigCell_parameters_symmetric A B C D hg).1 *
        levi A * upper ((A⁻¹).val * B) (bigCell_parameters_symmetric A B C D hg).2 := by
  have hL := (bigCell_parameters_symmetric A B C D hg).1
  have had := (SymplecticGroup.fromBlocks_mem_iff.mp hg).2.2
  have hD : D = C * (A⁻¹).val * B + (A⁻¹).val.transpose := by
    have h := congrArg (fun M => (A⁻¹).val.transpose * M) had
    simp only [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
      one_mul, mul_one] at h
    rw [hL.eq] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  apply Subtype.ext
  change Matrix.fromBlocks A.val B C D =
    Matrix.fromBlocks 1 0 (C * (A⁻¹).val) 1 *
      Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *
        Matrix.fromBlocks 1 ((A⁻¹).val * B) 0 1
  simp only [Matrix.fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero,
    zero_add, add_zero]
  have hC : C * (A⁻¹).val * A.val = C := by
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hB : A.val * ((A⁻¹).val * B) = B := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [hC, hB, hD, Matrix.mul_assoc C (A⁻¹).val B]

theorem subgroup_eq_top_of_generators (H : Subgroup (PoissonAutomorphyNormalizationData.Sp ι ℚ))
    (hU : ∀ (B : Matrix ι ι ℚ) (hB : B.IsSymm), upper B hB ∈ H)
    (hM : ∀ A : (Matrix ι ι ℚ)ˣ, levi A ∈ H)
    (hW : weyl ι ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  have hL : ∀ (B : Matrix ι ι ℚ) (hB : B.IsSymm), lower B hB ∈ H := by
    intro B hB
    rw [lower_conjugation]
    exact H.mul_mem (H.mul_mem hW (hU (-B) hB.neg)) (H.inv_mem hW)
  obtain ⟨X, hX, hdet⟩ := exists_upper_bigCell g
  let f := upper X hX * g
  obtain ⟨A, hA⟩ := (Matrix.isUnit_iff_isUnit_det f.val.toBlocks₁₁).mpr hdet
  have hmatrix : Matrix.fromBlocks A.val f.val.toBlocks₁₂
      f.val.toBlocks₂₁ f.val.toBlocks₂₂ = f.val := by
    rw [hA, Matrix.fromBlocks_toBlocks]
  have hs : Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁
      f.val.toBlocks₂₂ ∈ Matrix.symplecticGroup ι ℚ := by
    rw [hmatrix]
    exact f.property
  have hfactor := bigCell_factorization A f.val.toBlocks₁₂
    f.val.toBlocks₂₁ f.val.toBlocks₂₂ hs
  have hf : f ∈ H := by
    have heq : f = ⟨Matrix.fromBlocks A.val f.val.toBlocks₁₂
        f.val.toBlocks₂₁ f.val.toBlocks₂₂, hs⟩ :=
      Subtype.ext hmatrix.symm
    rw [heq, hfactor]
    exact H.mul_mem (H.mul_mem (hL _ _) (hM A)) (hU _ _)
  have h := H.mul_mem (H.inv_mem (hU X hX)) hf
  simpa only [f, inv_mul_cancel_left] using h

def transposeMulEquiv (A : (Matrix ι ι ℚ)ˣ) : (ι → ℚ) ≃ (ι → ℚ) where
  toFun x := A.val.transpose *ᵥ x
  invFun x := (A⁻¹).val.transpose *ᵥ x
  left_inv x := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
  right_inv x := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]

omit [DecidableEq ι] in
theorem map_quadratic (B : Matrix ι ι ℚ) (x : ι → ℚ) :
    algebraMap ℚ PoissonAutomorphyNormalizationData.AQ (1 / 2) *
      (PoissonAutomorphyNormalizationData.diagonal x ⬝ᵥ (B.map (algebraMap ℚ PoissonAutomorphyNormalizationData.AQ) *ᵥ PoissonAutomorphyNormalizationData.diagonal x)) =
      algebraMap ℚ PoissonAutomorphyNormalizationData.AQ ((1 / 2) * (x ⬝ᵥ (B *ᵥ x))) := by
  simp only [PoissonAutomorphyNormalizationData.diagonal, dotProduct, Matrix.mulVec, Matrix.map_apply,
    map_mul, map_sum]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

def thetaStabilizer : Subgroup (PoissonAutomorphyNormalizationData.Sp ι ℚ) where
  carrier := {γ | ∀ f : PoissonAutomorphyNormalizationData.adelicSchwartz ι,
    PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction γ f) = PoissonAutomorphyNormalizationData.thetaFunctional f}
  one_mem' := by intro f; simp
  mul_mem' := by
    intro γ δ hγ hδ f
    change PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction (γ * δ) f) = _
    rw [map_mul]
    exact (hγ (D.rationalAction δ f)).trans (hδ f)
  inv_mem' := by
    intro γ hγ f
    have h := hγ (D.rationalAction γ⁻¹ f)
    have hc : D.rationalAction γ (D.rationalAction γ⁻¹ f) = f := by
      change (D.rationalAction γ * D.rationalAction γ⁻¹) f = f
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hc] at h
    exact h.symm

theorem upper_mem_thetaStabilizer (B : Matrix ι ι ℚ) (hB : B.IsSymm) :
    upper B hB ∈ thetaStabilizer D := by
  intro f
  unfold PoissonAutomorphyNormalizationData.thetaFunctional
  apply tsum_congr
  intro x
  change (D.adelic.action (D.rationalSplit (upper B hB)) f).val (PoissonAutomorphyNormalizationData.diagonal x) = _
  rw [D.rational_quadratic (upper B hB) B hB rfl, map_quadratic,
    D.character_rational, one_mul]

theorem levi_mem_thetaStabilizer (A : (Matrix ι ι ℚ)ˣ) :
    levi A ∈ thetaStabilizer D := by
  intro f
  unfold PoissonAutomorphyNormalizationData.thetaFunctional
  calc
    (∑' x : ι → ℚ, (D.rationalAction (levi A) f).val (PoissonAutomorphyNormalizationData.diagonal x)) =
        ∑' x : ι → ℚ, f.val (PoissonAutomorphyNormalizationData.diagonal (transposeMulEquiv A x)) := by
      apply tsum_congr
      intro x
      change (D.adelic.action (D.rationalSplit (levi A)) f).val (PoissonAutomorphyNormalizationData.diagonal x) = _
      rw [D.rational_linear (levi A) A rfl]
      apply congrArg f.val
      exact funext fun i => (RingHom.map_mulVec (algebraMap ℚ PoissonAutomorphyNormalizationData.AQ) A.val.transpose x i).symm
    _ = ∑' x : ι → ℚ, f.val (PoissonAutomorphyNormalizationData.diagonal x) :=
      (transposeMulEquiv A).tsum_eq (fun x => f.val (PoissonAutomorphyNormalizationData.diagonal x))

/-- Once the adelic Fourier summation identity has been proved, the
generator calculation gives invariance under every rational symplectic matrix. -/
theorem theta_invariant_of_fourier_summation
    (hFourier : ∀ f : PoissonAutomorphyNormalizationData.adelicSchwartz ι,
      (∑' x : ι → ℚ, PoissonAutomorphyNormalizationData.fourier D.character (PoissonAutomorphyNormalizationData.adelicMeasure D.finiteMeasure)
        f.val (PoissonAutomorphyNormalizationData.diagonal x)) = PoissonAutomorphyNormalizationData.thetaFunctional f)
    (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) (f : PoissonAutomorphyNormalizationData.adelicSchwartz ι) :
    PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction γ f) = PoissonAutomorphyNormalizationData.thetaFunctional f := by
  have hW : weyl ι ∈ thetaStabilizer D := by
    intro φ
    unfold PoissonAutomorphyNormalizationData.thetaFunctional
    calc
      _ = ∑' x : ι → ℚ, PoissonAutomorphyNormalizationData.fourier D.character (PoissonAutomorphyNormalizationData.adelicMeasure D.finiteMeasure)
          φ.val (PoissonAutomorphyNormalizationData.diagonal x) := by
        apply tsum_congr
        intro x
        exact D.rational_fourier (weyl ι) rfl φ (PoissonAutomorphyNormalizationData.diagonal x)
      _ = _ := hFourier φ
  have htop := subgroup_eq_top_of_generators (thetaStabilizer D)
    (upper_mem_thetaStabilizer D) (levi_mem_thetaStabilizer D) hW
  have hγ : γ ∈ thetaStabilizer D := by rw [htop]; trivial
  exact hγ f

end

end OAI.RepresentationTheory.Theta.Generators.PoissonAutomorphyConstruction
