import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection

/-! # Pairing Projectors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.PairingProjectors

noncomputable section

/-! Conjugate projector adjoints for the original torsion-functor
points and actual canonical Poincare pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.PairingValues OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.CoefficientPerfection

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (n : ℕ) (τ : Gal(E/ℚ))

omit [IsAlgClosed k] [NumberField.IsCMField E] in
theorem nativeLift_prescribedComponent (T : Over (Spec (.of k)))
    (x : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    let z := AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x
    AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme (q ^ n) z.val z.property =
      AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme (q ^ n) x.val x.property ≫
        AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (ρ.map (j.projector iota hsplit n τ)) := by
  let z := AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x
  let a := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme (q ^ n) x.val x.property
  let p := ρ.map (j.projector iota hsplit n τ)
  have : IsMonHom p := ρ.preservesGroup _
  apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n))).mp
  have hright : (a ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap (q ^ n) p) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.abelian.scheme (q ^ n) =
      x.val ≫ p :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun w => a ≫ w) (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion (q ^ n) p)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun w => w ≫ p) (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.abelian.scheme (q ^ n) x.val x.property))))
  exact (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A.abelian.scheme (q ^ n) z.val z.property).trans hright.symm

theorem canonicalTorsionOrthogonal_projectors (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)
    (υ : Gal(E/ℚ)) (hυ : υ = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)
    (T : Over (Spec (.of k))) (x y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
        (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x) y ↔
      AbelianScheme.FrobeniusKernel.Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T x
        (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n υ T y) := by
  let e := Canonical.PairingValues.prescribedNativePairing A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
  let a := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme (q ^ n) x.val x.property
  let b := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A.abelian.scheme (q ^ n) y.val y.property
  let px := AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T x
  let py := AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n υ T y
  have hp := AbelianScheme.IsogenyQuotient.ProjectorAdjoints.Construction.l45_projectors_adjoint_of_integral_action j iota hsplit A.abelian ρ n e
    (Canonical.CoefficientPerfection.canonical_native_coefficient_adjoint A ρ hρ (q ^ n) _) τ T a b
  rw [← hυ] at hp
  have hv := (congrArg (fun w => e.pairValue w b) (nativeLift_prescribedComponent j iota hsplit A ρ n τ T x)).trans
    (hp.trans (congrArg (fun w => e.pairValue a w) (nativeLift_prescribedComponent j iota hsplit A ρ n υ T y).symm))
  exact (Canonical.PairingValues.canonicalTorsionOrthogonal_native A (q ^ n) _ T px y).trans
    ((Iff.of_eq (congrArg (fun w => w = 1) hv)).trans (Canonical.PairingValues.canonicalTorsionOrthogonal_native A (q ^ n) _ T x py).symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.PairingProjectors
