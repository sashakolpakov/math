import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRetraction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing

/-! # Conjugate Projectors -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ConjugateProjectors

noncomputable section

/-! Complex conjugation sends the actual integral projector to the
opposite embedding projector modulo q^n. The induced maps on actual
torsion functors are therefore equal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)

/-- This is the centrality of complex conjugation for a CM field,
proved through an actual complex embedding. -/
theorem rationalConjugation_commutes (τ : Gal(E/ℚ)) (x : E) :
    τ (Arithmetic.rationalConjugation E x) = Arithmetic.rationalConjugation E (τ x) := by
  let emb : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply emb.injective
  exact (NumberField.IsCMField.complexEmbedding_complexConj E (emb.comp τ.toRingHom) x).trans
    (NumberField.IsCMField.complexEmbedding_complexConj E emb (τ x)).symm

theorem localCharacter_conjugation (τ : Gal(E/ℚ)) (a : NumberField.RingOfIntegers E) :
    j.localCharacter iota τ (NumberField.IsCMField.ringOfIntegersComplexConj E a) =
      j.localCharacter iota (Arithmetic.rationalConjugation E * τ) a := by
  apply congrArg j.integralEmbedding
  apply NumberField.RingOfIntegers.ext
  exact congrArg iota (rationalConjugation_commutes τ a)

theorem conjugate_projector_coordinates (n : ℕ) (τ : Gal(E/ℚ)) :
    j.residueCoordinates iota n
      (NumberField.IsCMField.ringOfIntegersComplexConj E (j.projector iota hsplit n τ)) =
    j.residueCoordinates iota n (j.projector iota hsplit n (Arithmetic.rationalConjugation E * τ)) := by
  ext υ
  have hc (σ : Gal(E/ℚ)) : Arithmetic.rationalConjugation E * (Arithmetic.rationalConjugation E * σ) = σ := by
    rw [← mul_assoc, Models.rationalConjugation_mul_self, one_mul]
  calc
    _ = j.residueCoordinates iota n (j.projector iota hsplit n τ) (Arithmetic.rationalConjugation E * υ) :=
      congrArg (PadicInt.toZModPow n) (localCharacter_conjugation j iota υ (j.projector iota hsplit n τ))
    _ = (Pi.single τ 1 : Gal(E/ℚ) → ZMod (q ^ n)) (Arithmetic.rationalConjugation E * υ) := congrFun (j.projector_coordinates iota hsplit n τ) _
    _ = (Pi.single (Arithmetic.rationalConjugation E * τ) 1 : Gal(E/ℚ) → ZMod (q ^ n)) υ := by
      by_cases hυ : υ = Arithmetic.rationalConjugation E * τ
      · rw [hυ, hc]
        simp
      · have hne : Arithmetic.rationalConjugation E * υ ≠ τ := by
          intro h
          exact hυ ((hc υ).symm.trans (congrArg (fun σ => Arithmetic.rationalConjugation E * σ) h))
        simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hυ]
    _ = _ := (congrFun (j.projector_coordinates iota hsplit n (Arithmetic.rationalConjugation E * τ)) υ).symm

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

omit [NumberField.IsCMField E] in
theorem torsionProjection_inclusion (n : ℕ) (τ : Gal(E/ℚ)) :
    BlockRetraction.torsionProjectionNat j iota hsplit A ρ n τ ≫ BlocksProjectors.blockInclusion A ρ (j.localCharacter iota τ) n =
      DualityPairing.homOnTorsion A A (ρ.map (j.projector iota hsplit n τ)) (q ^ n) := by
  ext T x
  rfl

theorem conjugate_projector_on_torsion (n : ℕ) (τ : Gal(E/ℚ)) :
    DualityPairing.homOnTorsion A A (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E
      (j.projector iota hsplit n τ))) (q ^ n) =
    BlockRetraction.torsionProjectionNat j iota hsplit A ρ n (Arithmetic.rationalConjugation E * τ) ≫
      BlocksProjectors.blockInclusion A ρ (j.localCharacter iota (Arithmetic.rationalConjugation E * τ)) n := by
  rw [torsionProjection_inclusion]
  ext T x
  apply Subtype.ext
  exact BlockDecomposition.action_eq_of_coordinates j iota hsplit A ρ n _ _
    (conjugate_projector_coordinates j iota hsplit n τ) T.unop x.val x.property

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ConjugateProjectors
