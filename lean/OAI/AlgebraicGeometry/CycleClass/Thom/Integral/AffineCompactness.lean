import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.CharacterBound
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeAffineTopology
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Affine Compactness -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.AffineCompactness.Constructions

noncomputable section

/-! Integral complex algebra maps have compact inverse images of compact
sets in the actual character topology. Finite type on the base then gives
an ordinary proper continuous map. -/

open scoped NNReal

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.CharacterClosed.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.CharacterBound.Constructions

variable (A B : Type*) [CommRing A] [Algebra ℂ A]
  [CommRing B] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
  [Algebra.IsIntegral A B]

theorem isCompact_character_preimage (K : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)) (hK : IsCompact K) :
    IsCompact (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (IsScalarTower.toAlgHom ℂ A B) ⁻¹' K) := by
  let f := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (IsScalarTower.toAlgHom ℂ A B)
  let P := f ⁻¹' K
  have hb (b : B) : ∃ r : ℝ≥0, ∀ y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B,
      y ∈ P → ‖y b‖₊ ≤ r :=
    CharacterBound.Constructions.integralCharacter_norm_bound K hK b (Algebra.IsIntegral.isIntegral b)
  choose r hr using hb
  let j : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B → B → ℂ := fun y => y
  have hclosed : IsClosed (j '' P) :=
    (Affine.CharacterClosed.Constructions.isClosedEmbedding_character_coe B).isClosedMap P (hK.isClosed.preimage f.continuous)
  have hsub : j '' P ⊆ Set.pi Set.univ (fun b => Metric.closedBall (0 : ℂ) (r b : ℝ)) := by
    rintro _ ⟨y, hy, rfl⟩ b _
    change dist (y b) 0 ≤ (r b : ℝ)
    rw [dist_zero_right]
    exact hr b y hy
  have hc := (isCompact_univ_pi (fun b => isCompact_closedBall (0 : ℂ) (r b : ℝ))).of_isClosed_subset
    hclosed hsub
  exact Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isEmbedding_coe.isCompact_iff.mpr hc

theorem isProperMap_character_comap [Algebra.FiniteType ℂ A] :
    IsProperMap (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (IsScalarTower.toAlgHom ℂ A B)) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  exact ⟨(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (IsScalarTower.toAlgHom ℂ A B)).continuous,
    fun K hK => isCompact_character_preimage A B K hK⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.AffineCompactness.Constructions
