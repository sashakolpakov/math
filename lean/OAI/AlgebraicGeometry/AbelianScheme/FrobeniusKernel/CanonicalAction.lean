import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionActions

/-! # Canonical Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalAction.Construction

noncomputable section

/-! The canonical full kernel carries its descended integral action;
stability follows from its exact independent all-test prescription. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
variable (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

theorem canonicalFullKernel_stable (r : NumberField.RingOfIntegers E)
    (T : Over (Spec (.of k)))
    (z : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit A ρ n s labels P H).X) :
    ∃ z' : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit A ρ n s labels P H).X,
      z' ≫ Canonical.Construction.canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H =
        (z ≫ Canonical.Construction.canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H) ≫ ρ.map r := by
  let a := z ≫ Canonical.Construction.canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H
  have ha := (CanonicalPoints.Construction.canonicalFullKernel_realizes j iota hsplit A ρ hρ hgood n s labels hc P H T a).mp ⟨z, rfl⟩
  exact (CanonicalPoints.Construction.canonicalFullKernel_realizes j iota hsplit A ρ hρ hgood n s labels hc P H T (a ≫ ρ.map r)).mpr
    (PrescriptionActions.Construction.prescribedFullKernel_action A j iota hsplit ρ n s labels H r T a ha)

def canonicalFullQuotientAction : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E)
    (Canonical.Construction.canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).abelian :=
  (Canonical.Construction.canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).action ρ
    (canonicalFullKernel_stable j iota hsplit A ρ hρ hgood n s labels hc P H)

theorem canonicalFullQuotientAction_intertwines (r : NumberField.RingOfIntegers E) :
    (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom ≫
      (canonicalFullQuotientAction j iota hsplit A ρ hρ hgood n s labels hc P H).map r =
        ρ.map r ≫ (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom :=
  QuotientActionBase.Construction.quotientAction_intertwines ρ
    (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H)
    ((Canonical.Construction.canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).actionStableKernel_of_subgroup
      ρ (canonicalFullKernel_stable j iota hsplit A ρ hρ hgood n s labels hc P H)) r

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalAction.Construction
