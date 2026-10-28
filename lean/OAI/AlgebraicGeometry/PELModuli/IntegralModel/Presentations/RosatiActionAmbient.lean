import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.AllTestGraphBounds
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.ActionScheme

/-! # Rosati Action Ambient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RosatiActionAmbient

noncomputable section

/-! The full corrected Presentations equations input constructs a finite-type
integral-action ambient containing every Rosati-compatible action on every
test scheme over a fixed geometric polarized abelian variety. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_e34_bounded_action_ambient_for_rosati
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (hPresentations : Hilbert.EndomorphismEquationsInput.{0})
    (hc : ∀ s : Spec (.of k), IsUnit (D.conductor : (Spec (.of k)).presheaf.stalk s)) :
    ∃ Z : Over (Spec (.of k)), LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsSeparated Z.hom ∧
      ∃ ρZ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback Z.hom),
        ∀ (T : Over (Spec (.of k)))
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.abelian.pullback T.hom)),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ →
            ∃! f : T ⟶ Z, Integral.ActionScheme.restrictIntegralAction A.abelian ρZ f = ρ := by
  obtain ⟨BA, Q, hQ⟩ := D.exists_e34_integral_generator_bound_on_all_tests A
  obtain ⟨B, L, M, hSegre, hft, hqc, hsep, ρZ, _, hclass⟩ :=
    ActionScheme.exists_e34_bounded_integral_action_scheme A.abelian D hPresentations BA hc (fun _ => Q)
  exact ⟨M.solutionScheme, hft, hqc, hsep, ρZ,
    fun T ρ hρ => (hclass T ρ).mp (hQ B hSegre T ρ hρ)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.RosatiActionAmbient
