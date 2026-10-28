import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceIsotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.Labels

/-! # Points Choice Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsChoiceIsotropy.Construction

noncomputable section

/-!
The CMPoints residue projectors discharge completeness and orthogonality in
the exact-kernel isotropy theorem. Labels may be taken to be the actual
CM conjugate indexing constructed in CMLabels.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E F : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field F] [NumberField F] {κ : F →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice F κ q) (iota : E →+* F) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (h s : ℕ) (labels : ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))

local notation "chosenProj" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels
local notation "oppositeProj" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels

theorem l45_choice_torsion_orthogonal :
    ∀ i k : ChoiceKernel.Construction.KernelIndex s, i ≠ k →
      ChoiceIsotropy.Construction.choiceTorsionProjector (q ^ h) s chosenProj oppositeProj i ≫
        ChoiceIsotropy.Construction.choiceTorsionProjector (q ^ h) s chosenProj oppositeProj k = 1 := by
  intro i k hik
  have hh := PointsProjectorSum.Construction.l45_native_projectors_orthogonal j iota hsplit A σ h
    (labels i) (labels k) (fun he => hik (labels.injective he))
  cases i <;> cases k <;> exact hh

theorem l45_choice_torsion_complete :
    (∏ i, ChoiceIsotropy.Construction.choiceTorsionProjector (q ^ h) s chosenProj oppositeProj i) =
      𝟙 (Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h)) := by
  calc
    _ = ∏ i, Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (σ.map (j.projector iota hsplit h (labels i))) := by
      apply Finset.prod_congr rfl
      intro i _
      cases i <;> rfl
    _ = ∏ τ : Gal(E/ℚ), Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (σ.map (j.projector iota hsplit h τ)) :=
      labels.prod_comp (fun τ => Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (σ.map (j.projector iota hsplit h τ)))
    _ = _ := PointsProjectorSum.Construction.l45_native_projectors_complete j iota hsplit A σ h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsChoiceIsotropy.Construction
