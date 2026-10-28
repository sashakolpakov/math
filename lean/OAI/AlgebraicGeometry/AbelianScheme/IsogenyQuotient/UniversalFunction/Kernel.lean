import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PairingAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PairingAlternation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.Isotropic

/-! # Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Kernel.Construction

noncomputable section

/-! The original PEL family with universal global functions constructs its universal
isotropic quotient using its own canonical polarization pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

theorem universalFunction_universal_isotropic_native_quotient
    {E K L : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L] {κ : L →+* ℂ}
    {d N : ℕ} {D : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
    {T : Over (Spec (.of K))} (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject D iota N T)
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.polarized.abelian.scheme)
    (q : ℕ) [Fact q.Prime] (hcop : Nat.Coprime q N) (h : ℕ)
    (hdegree : Nat.Coprime (q ^ h) ((∏ i, D.polarizationType i) ^ 2))
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
    (hsplit : j.HasSplitCoordinates arithmeticEmbedding) (labels : ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (M : Fin d → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module (ZMod (q ^ h)) (M i)] [∀ i, Finite (M i)]
    (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) :
    let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
    let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
    let b := PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
    let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels b
    Universal.Isotropic.Construction.UniversalIsotropicNativeFamily A (q ^ h) M p r b ep := by
  let hn := pow_pos (Fact.out : q.Prime).pos h
  let b := PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
    A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA)
    (q ^ h) hn
  apply Universal.Isotropic.Construction.universal_isotropic_native_quotient A q hcop h j arithmeticEmbedding hsplit labels hlabels M b
  · exact PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing_isPerfect A.polarized.abelian A.polarized.dual
      A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) (q ^ h) hn hdegree
  · exact PairingAlternation.Construction.universalFunctionNativePolarizationPairing_alternating A.polarized.dual (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) A.polarized.polarization
      (q ^ h) hn T.hom
  · exact PairingAdjoints.Construction.universalFunctionNativePolarizationPairing_coefficient_adjoint A.polarized (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) A.action A.rosati
      (q ^ h) hn
  · exact h_FiniteDescent

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Kernel.Construction
