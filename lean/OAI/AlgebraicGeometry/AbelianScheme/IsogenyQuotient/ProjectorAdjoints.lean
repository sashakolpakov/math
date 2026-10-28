import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ConjugateProjectors
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SourcePairingFormula

/-! # Projector Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProjectorAdjoints.Construction

noncomputable section

/-!
The CM Rosati adjoint equation for the integral action implies adjointness
of the actual residue projectors. The congruence of conjugate lifts is
proved before restricting to torsion. This isolates the remaining passage
from the Poincare Rosati equation to the canonical torsion pairing.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (n : ℕ)
  {W : Over S} [GrpObj W]
  (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ n))
    (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ n)) (W := W))

theorem l45_projectors_adjoint_of_integral_action
    (hOE : ∀ (a : NumberField.RingOfIntegers E) (X : Over S)
      (x y : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ n)),
      b.pairValue (x ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map a)) y =
        b.pairValue x (y ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ n)
          (σ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))))
    (τ : Gal(E/ℚ)) (X : Over S) (x y : X ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ n)) :
    b.pairValue (x ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ n) (σ.map (j.projector iota hsplit n τ))) y =
      b.pairValue x (y ≫ Torsion.Groups.Construction.nativeTorsionMap (q ^ n)
        (σ.map (j.projector iota hsplit n (PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ)))) := by
  have hh := hOE (j.projector iota hsplit n τ) X x y
  rw [ConjugateProjectors.Construction.l45_native_projector_conjugate j iota hsplit A σ n τ] at hh
  exact hh

omit [Field K] [NumberField K] [Fact q.Prime] [GrpObj W] in
theorem cmConjugateLabels_swap [IsGalois ℚ E]
    (s : ℕ) (hdegree : Module.finrank ℚ E = 2 * s)
    (chosen : Set Gal(E/ℚ))
    (hchosen : ∀ τ, τ ∈ chosen ↔ PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ ∉ chosen)
    (i : Fin s ⊕ Fin s) :
    CM.Labels.Construction.cmConjugateLabels s hdegree chosen hchosen (Sum.swap i) =
      PELModuli.CMPoints.Arithmetic.rationalConjugation E * CM.Labels.Construction.cmConjugateLabels s hdegree chosen hchosen i := by
  cases i with
  | inl i => exact CM.Labels.Construction.cmConjugateLabels_opposite s hdegree chosen hchosen i
  | inr i =>
      change CM.Labels.Construction.cmConjugateLabels s hdegree chosen hchosen (Sum.inl i) = _
      rw [CM.Labels.Construction.cmConjugateLabels_opposite]
      exact (CM.Labels.Construction.cmConjugation_involutive _).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProjectorAdjoints.Construction
