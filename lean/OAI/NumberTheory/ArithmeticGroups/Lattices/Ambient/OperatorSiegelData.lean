import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeMatrixOperatorLift
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.TriangularConjugates

/-! # Operator Siegel Data -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.OperatorSiegelData.Construction

noncomputable section

section

/-! Concrete compact, diagonal, and upper-unitriangular regions in the
volume-preserving operator group for ambient lattice reduction. -/

open Set _root_.ContinuousLinearMap
open scoped Classical Pointwise

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def ambientUpperCompact {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (c : ℝ) :
    Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
  VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b ⁻¹' {g | UpperUnitriangularMatrices.Construction.IsUpperUnitriangular g.val ∧ ∀ i j, |g.val i j| ≤ c}

def ambientSiegelUnipotent {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) := (ambientUpperCompact b 1)⁻¹

def ambientSiegelDiagonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
  {a | ∃ d : Fin m → ℝ, (∀ i, 0 < d i) ∧
    (∀ i j, i.val + 1 = j.val → d i ≤ 2 * d j) ∧
      (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b a⁻¹).val = Matrix.diagonal d}

def ambientSiegelCompact : Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :=
  Subtype.val ⁻¹' (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup (0 : L →L[ℝ] L →L[ℝ] L) : Set (L →L[ℝ] L)ˣ)

theorem ambientUpperCompact_isCompact {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (c : ℝ) :
    IsCompact (ambientUpperCompact b c) :=
  (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom_isClosedEmbedding b).isCompact_preimage
    (UpperUnitriangularMatrices.Construction.bounded_upper_unitriangular_isCompact m c)

theorem ambientSiegelUnipotent_isCompact {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    IsCompact (ambientSiegelUnipotent b) := (ambientUpperCompact_isCompact b 1).inv

theorem ambientSiegelUnipotent_upper {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (hg : g ∈ ambientSiegelUnipotent b) :
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b g).val := by
  have he : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b g⁻¹).val := hg.1
  have hi := he.unit_inv (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b g⁻¹)
  simpa only [map_inv, inv_inv] using hi

theorem ambientSiegelCompact_isCompact : IsCompact (ambientSiegelCompact (L := L)) :=
  VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits_isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup_isCompact 0)

theorem ambientSiegelCompact_cartan (k : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (hk : k ∈ ambientSiegelCompact) : OperatorCartanInvolution.Construction.volumeOperatorCartanHom k = k := by
  apply Subtype.ext
  apply Units.ext
  change adjoint (k.val⁻¹).val = k.val.val
  have he := OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnit_adjoint_eq_inv (0 : L →L[ℝ] L →L[ℝ] L) k.val⁻¹
    ((OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup (0 : L →L[ℝ] L →L[ℝ] L)).inv_mem hk)
  simpa only [inv_inv] using he

theorem ambientSiegelDiagonal_cartan {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (ha : a ∈ ambientSiegelDiagonal b) :
    OperatorCartanInvolution.Construction.volumeOperatorCartanHom a = a⁻¹ := by
  obtain ⟨d, _, _, hd⟩ := ha
  exact VolumeMatrixOperatorLift.Construction.volumeOperatorCartanHom_diagonal b a d hd

end

/-! Both conjugated unipotent families in the reflection argument
have compact containers for the concrete ambient diagonal chamber. -/

open Set
open scoped Classical Pointwise

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem volume_operator_compact_diagonal_conjugates {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (C : Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))) (hC : IsCompact C)
    (htri : ∀ u ∈ C, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b u).val)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)), IsCompact D ∧
      ∀ (d : Fin m → ℝ), (∀ i, 0 < d i) → (∀ i j, i ≤ j → d i / d j ≤ R) →
        ∀ a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L),
          (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b a).val = Matrix.diagonal d → ∀ u ∈ C, a * u * a⁻¹ ∈ D := by
  let F := VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b
  have hF := VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom_isClosedEmbedding b
  obtain ⟨D, hD, hbound⟩ := Compact.TriangularConjugates.Construction.compact_upper_diagonal_conjugates (F '' C) (hC.image hF.continuous)
    (by rintro _ ⟨u, hu, rfl⟩; exact htri u hu) R hR
  refine ⟨F ⁻¹' D, hF.isCompact_preimage hD, fun d hd hratio a ha u hu => ?_⟩
  have he := hbound d hd hratio (F a) ha (F u) ⟨u, hu, rfl⟩
  simpa only [Set.mem_preimage, map_mul, map_inv] using he

theorem ambientSiegel_compact_conjugates {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (C : Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))) (hC : IsCompact C)
    (htri : ∀ u ∈ C, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b u).val) :
    ∃ D D₂ : Set (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)), IsCompact D ∧ IsCompact D₂ ∧
      (∀ a ∈ ambientSiegelDiagonal b, ∀ u ∈ C, a⁻¹ * u * a ∈ D) ∧
      (∀ a ∈ ambientSiegelDiagonal b, ∀ u ∈ C, a⁻¹ * a⁻¹ * u⁻¹ * a * a ∈ D₂) := by
  obtain ⟨D, hD, hfirst⟩ := volume_operator_compact_diagonal_conjugates b C hC htri
    ((2 : ℝ) ^ m) (by positivity)
  have htriInv : ∀ u ∈ C⁻¹, UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b u).val := by
    intro u hu
    have he := (htri u⁻¹ hu).unit_inv (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b u⁻¹)
    simpa only [map_inv, inv_inv] using he
  obtain ⟨D₂, hD₂, hsecond⟩ := volume_operator_compact_diagonal_conjugates b C⁻¹ hC.inv htriInv
    (((2 : ℝ) ^ m) ^ 2) (sq_nonneg _)
  refine ⟨D, D₂, hD, hD₂, ?_, ?_⟩
  · rintro a ⟨d, hd, hstep, ha⟩ u hu
    simpa only [inv_inv] using hfirst d hd (DiagonalChamberRatios.Construction.positive_gap_chain_ratio d hd hstep) a⁻¹ ha u hu
  · rintro a ⟨d, hd, hstep, ha⟩ u hu
    have hs : ∀ i j, i ≤ j → (d i) ^ 2 / (d j) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 := by
      intro i j hij
      rw [← div_pow]
      exact (sq_le_sq₀ (div_nonneg (hd i).le (hd j).le) (by positivity)).mpr
        (DiagonalChamberRatios.Construction.positive_gap_chain_ratio d hd hstep i j hij)
    have hdiag : (VolumeMatrixOperatorLift.Construction.volumeOperatorMatrixHom b (a⁻¹ * a⁻¹)).val =
        Matrix.diagonal (fun i => (d i) ^ 2) := by
      rw [map_mul, Units.val_mul, ha, Matrix.diagonal_mul_diagonal]
      simp only [pow_two]
    have hi : u⁻¹ ∈ C⁻¹ := by simpa only [Set.mem_inv, inv_inv] using hu
    have he := hsecond (fun i => (d i) ^ 2) (fun i => sq_pos_of_pos (hd i)) hs
      (a⁻¹ * a⁻¹) hdiag u⁻¹ hi
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.OperatorSiegelData.Construction
