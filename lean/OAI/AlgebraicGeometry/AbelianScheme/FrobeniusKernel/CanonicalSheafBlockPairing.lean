import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints

/-! # Canonical Sheaf Block Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockPairing.Construction

noncomputable section

/-! Conjugate coefficient blocks pair perfectly under the independently
specified canonical CartierDuality polarization pairing. Their annihilator geometry
is derived from the complete accepted duality theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n : ℕ) (τ : Gal(E/ℚ))

omit [IsAlgClosed k] in
theorem canonicalBlockSheafConjugateProjector_eq :
    CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) ≫
      CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) =
        CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme
          (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E
            (j.projector iota hsplit n τ))))) (q ^ n) := by
  have h := (PELModuli.CMPoints.ConjugateProjectors.conjugate_projector_on_torsion j iota hsplit A.abelian ρ n τ).trans
    (PELModuli.CMPoints.ConjugateProjectors.torsionProjection_inclusion j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ))
  exact (CanonicalSheafBlockPoints.Construction.canonicalBlockSheafProjector_eq j iota hsplit A.abelian ρ n
    (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)).trans
      (PrescriptionActions.Construction.originalTorsionSheafMap_eq_of_action A.abelian (q ^ n) _ _ h).symm

def canonicalSheafBlockPairing :
    CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheaf j iota hsplit A.abelian ρ n τ)
      (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheaf j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)) :=
  (CartierDualityCanonical.Construction.e56SourceTorsionPairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)).restrict
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n τ)
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ))

theorem canonicalSheafBlockProjectors_adjoint (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) :
    CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint (CartierDualityCanonical.Construction.e56SourceTorsionPairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n))
      (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A.abelian ρ n τ ≫
        CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n τ)
      (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) ≫
        CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)) := by
  have h := SourcePolarizationAdjoints.Construction.sourceCanonicalPairing_coefficient_adjoint A ρ hρ (q ^ n)
    (pow_pos (Fact.out : q.Prime).pos n) (j.projector iota hsplit n τ)
  exact (congrArg₂ (fun a b => CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint
    (CartierDualityCanonical.Construction.e56SourceTorsionPairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)) a b)
    (CanonicalSheafBlockPoints.Construction.canonicalBlockSheafProjector_eq j iota hsplit A.abelian ρ n τ)
    (canonicalBlockSheafConjugateProjector_eq j iota hsplit A ρ n τ)).mpr h

omit [NumberField.IsCMField E] in
theorem canonicalBlockSheaf_finiteLocallyFree :
    CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb (Spec (.of k)) (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheaf j iota hsplit A.abelian ρ n τ) :=
  (CartierDualityCanonical.Construction.e56SourceTorsion_finiteLocallyFree A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)).of_retract
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n τ)
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A.abelian ρ n τ)
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafRetraction j iota hsplit A.abelian ρ n τ)

theorem canonicalSheafBlockPairing_isPerfect (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (hgood : q.Coprime (∏ i, δ i)) :
    (canonicalSheafBlockPairing j iota hsplit A ρ n τ).IsPerfect :=
  CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_isPerfect _ (CartierDualityCanonical.Construction.e56SourcePrimePowerPairing_isPerfect A hgood n)
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n τ)
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A.abelian ρ n τ)
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafRetraction j iota hsplit A.abelian ρ n τ)
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafInclusion j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ))
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafProjection j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ))
    (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheafRetraction j iota hsplit A.abelian ρ n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ))
    (canonicalSheafBlockProjectors_adjoint j iota hsplit A ρ n τ hρ)

theorem canonicalSheafBlockAnnihilator_duality (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (hgood : q.Coprime (∏ i, δ i))
    (H : Subobject (CanonicalSheafBlockRetraction.Construction.canonicalBlockSheaf j iota hsplit A.abelian ρ n τ))
    (hH : CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec (.of k)))) :
    let e := canonicalSheafBlockPairing j iota hsplit A ρ n τ
    CartierDuality.PolarizedTorsion.FiniteLocallyFreeRepresentable (CartierDuality.PolarizedTorsion.annihilator e H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec (.of k))) ∧
      IsIso (CartierDuality.PolarizedTorsion.annihilatorToQuotientDual e H) ∧
      CartierDuality.PolarizedTorsion.annihilator e.flip (CartierDuality.PolarizedTorsion.annihilator e H) = H ∧
      ∀ (T : Scheme) (f : T ⟶ Spec (.of k)),
        CartierDuality.PolarizedTorsion.baseChangeSubobject f (CartierDuality.PolarizedTorsion.annihilator e H) =
          CartierDuality.PolarizedTorsion.annihilator (CartierDuality.PolarizedTorsion.baseChangePairing f e) (CartierDuality.PolarizedTorsion.baseChangeSubobject f H) :=
  CartierDuality.PolarizedTorsion.annihilator_duality (canonicalSheafBlockPairing j iota hsplit A ρ n τ) H
    (canonicalSheafBlockPairing_isPerfect j iota hsplit A ρ n τ hρ hgood)
    (canonicalBlockSheaf_finiteLocallyFree j iota hsplit A ρ n τ) hH

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalSheafBlockPairing.Construction
