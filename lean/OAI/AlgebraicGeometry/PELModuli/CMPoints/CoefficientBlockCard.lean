import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientLattice
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockCard

/-! # Coefficient Block Card -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientBlockCard

noncomputable section

/-! Actual complex coefficient blocks have cardinal q^(r*n) when the
native rational period module has coefficient rank r. In particular a
full CM field action has height-one block cardinalities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)

theorem coefficient_projector_card_of_coordinates {V : Type*} [AddCommGroup V]
    [Module (NumberField.RingOfIntegers E) V] (r n : ℕ)
    (e : V
      ≃ₗ[NumberField.RingOfIntegers E]
        (Fin r → NumberField.RingOfIntegers E ⧸
          Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E))))
    (τ : Gal(E/ℚ)) :
    Nat.card {x : V //
      (j.projector iota hsplit n τ) • x = x} = q ^ (r * n) := by
  let e₁ := CoordinateBlocks.scalarFixedEquiv e (j.projector iota hsplit n τ)
  let e₂ := CoordinateBlocks.quotientCoordinateBlockEquiv (I := Fin r)
    (Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)))
    (LatticeBlocks.splitCoefficientEquiv j iota hsplit n) (j.projector iota hsplit n τ) τ
    (LatticeBlocks.splitCoefficientEquiv_projector j iota hsplit n τ)
  rw [Nat.card_congr (e₁.trans e₂)]
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul, Nat.mul_comm n r]

variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

include hsplit in
theorem complex_coefficient_block_card_of_coordinates (r n : ℕ)
    (e : let := IntrinsicLattice.nativeAmbientModule A P ρ
      ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (IntrinsicLattice.nativeIntegerLattice A P ρ) (q ^ n)
      ≃ₗ[NumberField.RingOfIntegers E]
        (Fin r → NumberField.RingOfIntegers E ⧸
          Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E))))
    (τ : Gal(E/ℚ)) :
    Nat.card (BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n
      (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = q ^ (r * n) := by
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  let : NeZero (q ^ n) := ⟨pow_ne_zero n (Fact.out : q.Prime).ne_zero⟩
  let d : ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (IntrinsicLattice.nativeIntegerLattice A P ρ) (q ^ n)
      ≃ₗ[NumberField.RingOfIntegers E] LatticeDivision.moduleTorsion (IntrinsicLattice.nativeIntegerLattice A P ρ) (q ^ n) := by
    rw [← Nat.cast_pow]
    exact LatticeDivision.latticeDivisionEquiv (IntrinsicLattice.nativeIntegerLattice A P ρ) (q ^ n)
  let f := (CoordinateBlocks.scalarFixedEquiv d (j.projector iota hsplit n τ)).trans
    ((IntrinsicTorusAction.nativeTorsionFixedEquiv A P ρ (q ^ n) (j.projector iota hsplit n τ)).trans
      (ComplexBlockCard.fixedTorsionBlockEquiv j iota hsplit A ρ n τ))
  rw [← Nat.card_congr f]
  exact coefficient_projector_card_of_coordinates j iota hsplit r n e τ

include P in
theorem exists_complex_coefficient_block_bound (r : ℕ) (hr : Module.finrank ℚ E * r = 2 * g) :
    ∃ D : ℕ, 0 < D ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ j' : Arithmetic.QadicChoice K κ p, j'.HasSplitCoordinates iota → D < p →
        ∀ (n : ℕ) (τ : Gal(E/ℚ)),
          Nat.card (BlocksProjectors.blockPoints A ρ (j'.localCharacter iota τ) n
            (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = p ^ (r * n) := by
  obtain ⟨D, hD, hquot⟩ := IntrinsicCoefficientLattice.exists_native_coefficient_lattice_bound A P ρ r hr
  refine ⟨D, hD, fun p hp => ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  intro j' hsplit' hb n τ
  obtain ⟨e⟩ := hquot p hp hb n
  exact complex_coefficient_block_card_of_coordinates j' iota hsplit' A P ρ r n e τ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CoefficientBlockCard
