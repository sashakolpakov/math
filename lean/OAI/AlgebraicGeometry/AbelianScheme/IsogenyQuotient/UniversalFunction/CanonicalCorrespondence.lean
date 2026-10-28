import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Kernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Target

/-! # Canonical Correspondence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.CanonicalCorrespondence.Construction

noncomputable section

/-! The canonical polarization of a PEL family with universal global functions constructs
the finite etale correspondence of subgroup choices and actual fine targets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

theorem universalFunction_canonical_fine_correspondence
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
    (h_FiniteDescent : IsogenyComplement.Construction.FiniteDescentInput.{0}) (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel D iota N) (hZ : Z.IsFine) :
    let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
    let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels
    let b := PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization (GlobalFunctions.Construction.universalGlobalFunctions_of_finiteFlat_source A.polarized.polarization.isogeny.hom hA) (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
    let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j arithmeticEmbedding hsplit A.polarized.abelian A.action h d labels b
    Noetherian.UniversalTarget.Construction.UniversalFinePELFamily A (q ^ h) M p r ep Z := by
  apply Target.Construction.universalFunction_universal_fine_target A hA (q ^ h) (pow_pos (Fact.out : q.Prime).pos h) M
  · exact Kernel.Construction.universalFunction_universal_isotropic_native_quotient A hA q hcop h hdegree j arithmeticEmbedding
      hsplit labels hlabels M h_FiniteDescent
  · exact hdegree
  · exact hZ

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.CanonicalCorrespondence.Construction
