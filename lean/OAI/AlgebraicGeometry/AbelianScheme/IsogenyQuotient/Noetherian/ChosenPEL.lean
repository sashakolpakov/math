import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.UniversalKernel

/-! # Chosen PEL -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.ChosenPEL.Construction

noncomputable section

/-! Every individual subgroup choice has an independently constructed positive
PEL quotient with its exact full kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

theorem noetherian_chosen_pel_quotient
    {E K L : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L] {κ : L →+* ℂ}
    {d N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left] (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T)
    (q : ℕ) [Fact q.Prime] (hcop : Nat.Coprime q N) (h : ℕ)
    (hdegree : Nat.Coprime (q ^ h) ((∏ i, D.polarizationType i) ^ 2))
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
    (hsplit : j.HasSplitCoordinates arithmeticEmbedding) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (M : Fin d → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module (ZMod (q ^ h)) (M i)] [∀ i, Finite (M i)]
    (Q : Over T.left) [IsLocallyNoetherian Q.left] (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) :
    let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
    let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
    let b := PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
    let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels b
    ∀ U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M i) (p i) Q,
      RelativePEL.Construction.RelativePELQuotient A Q (ChoiceKernel.Construction.choiceFullKernel (q ^ h) d M p r ep U) (q ^ h) := by
  let hn := pow_pos (Fact.out : q.Prime).pos h
  let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
  let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
  let b := PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual A.polarized.polarization (q ^ h) hn
  let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels b
  change ∀ U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A.polarized.abelian.scheme (q ^ h) (M i) (p i) Q,
    RelativePEL.Construction.RelativePELQuotient A Q (ChoiceKernel.Construction.choiceFullKernel (q ^ h) d M p r ep U) (q ^ h)
  intro U
  have hsep : ∀ i k : ChoiceKernel.Construction.KernelIndex d, i ≠ k →
      Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (ChoiceKernel.Construction.choiceKernelProjector d p r k) ≫
        Torsion.Groups.Construction.nativeTorsionMap (q ^ h) (ChoiceKernel.Construction.choiceKernelProjector d p r i) = 1 := by
    intro i k hik
    exact CM.PointsChoiceIsotropy.Construction.l45_choice_torsion_orthogonal j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels k i hik.symm
  let R := MultiplicativeChoiceKernel.Construction.multiplicativeChoiceFullKernel_model (q ^ h) d p r ep M U T.hom hn hsep
  apply RelativePEL.Construction.noetherian_relative_pel_quotient_from_FiniteDescent A Q _ R (q ^ h) hn
    (ChoiceKernel.Construction.choiceFullKernel_killed (q ^ h) d M p r ep U) (hcop.pow_left h) hdegree
  · intro a
    apply BlockStability.Construction.choiceFullKernel_stable (q ^ h) d M p r ep U (A.action.map a)
      (fun i => ((j.residueCharacter arithmeticEmbedding (labels i) h a).val : ℤ))
    intro i
    have hc := CM.PointsProjectorSum.Construction.l45_native_projector_scalar j arithmeticEmbedding hsplit A.polarized.abelian A.action h (labels i) a
    cases i <;> exact hc
  · apply CM.PointsPerfectKernel.Construction.l45_choice_kernel_self_annihilating_from_perfect_source j arithmeticEmbedding hsplit
      A.polarized.abelian A.action h d labels b T.hom hlabels M U
    · exact PolarizationAdapter.Construction.noetherianNativePolarizationPairing_isPerfect A.polarized.abelian A.polarized.dual
        A.polarized.polarization (q ^ h) hn hdegree
    · exact PairingAlternation.Construction.noetherianNativePolarizationPairing_alternating A.polarized.dual A.polarized.polarization
        (q ^ h) hn T.hom
    · exact PairingAdjoints.Construction.noetherianNativePolarizationPairing_coefficient_adjoint A.polarized A.action A.rosati (q ^ h) hn
  · exact h_FiniteDescent

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.ChosenPEL.Construction
