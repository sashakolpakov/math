import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicTorusAction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

/-! # Complex Block Card -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockCard

noncomputable section

/-! Count the actual embedding-labelled complex torsion points using
the native exponential, the integral lattice, and the split projectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def fixedTorsionBlockEquiv (n : ℕ) (τ : Gal(E/ℚ)) :
    {x : A.torsionPoints (q ^ n) (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) //
      x.val ≫ ρ.map (j.projector iota hsplit n τ) = x.val} ≃
      BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) where
  toFun x := ⟨x.val.val, (BlocksProjectors.mem_block_iff_fixed j iota hsplit A ρ n τ _ x.val.val).mpr
    ⟨x.val.property, x.property⟩⟩
  invFun x :=
    let h := (BlocksProjectors.mem_block_iff_fixed j iota hsplit A ρ n τ _ x.val).mp x.property
    ⟨⟨x.val, h.1⟩, h.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

include hsplit in
theorem complex_block_card_of_coordinates (n : ℕ)
    (e : let := IntrinsicLattice.nativeAmbientModule A P ρ
      ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (IntrinsicLattice.nativeIntegerLattice A P ρ) (q ^ n)
      ≃ₗ[NumberField.RingOfIntegers E]
        (Fin 3 → NumberField.RingOfIntegers E ⧸
          Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E))))
    (τ : Gal(E/ℚ)) :
    Nat.card (BlocksProjectors.blockPoints A ρ (j.localCharacter iota τ) n
      (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = q ^ (3 * n) := by
  let := IntrinsicLattice.nativeAmbientModule A P ρ
  let : NeZero (q ^ n) := ⟨pow_ne_zero n (Fact.out : q.Prime).ne_zero⟩
  let d : ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (IntrinsicLattice.nativeIntegerLattice A P ρ) (q ^ n)
      ≃ₗ[NumberField.RingOfIntegers E] LatticeDivision.moduleTorsion (IntrinsicLattice.nativeIntegerLattice A P ρ) (q ^ n) := by
    rw [← Nat.cast_pow]
    exact LatticeDivision.latticeDivisionEquiv (IntrinsicLattice.nativeIntegerLattice A P ρ) (q ^ n)
  let f := (CoordinateBlocks.scalarFixedEquiv d (j.projector iota hsplit n τ)).trans
    ((IntrinsicTorusAction.nativeTorsionFixedEquiv A P ρ (q ^ n) (j.projector iota hsplit n τ)).trans
      (fixedTorsionBlockEquiv j iota hsplit A ρ n τ))
  rw [← Nat.card_congr f]
  exact LatticeBlocks.projector_card_of_coordinates j iota hsplit n e τ

include P in
theorem exists_complex_block_bound (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ D : ℕ, 0 < D ∧ ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ∀ j' : Arithmetic.QadicChoice K κ p, j'.HasSplitCoordinates iota → D < p →
        ∀ (n : ℕ) (τ : Gal(E/ℚ)),
          Nat.card (BlocksProjectors.blockPoints A ρ (j'.localCharacter iota τ) n
            (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) = p ^ (3 * n) := by
  obtain ⟨D, hD, hquot⟩ := IntrinsicLattice.exists_native_lattice_bound A P ρ s hs hg hdegree
  refine ⟨D, hD, fun p hp => ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  intro j' hsplit' hb n τ
  obtain ⟨e⟩ := hquot p hp hb n
  exact complex_block_card_of_coordinates j' iota hsplit' A P ρ n e τ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexBlockCard
