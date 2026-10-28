import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.AssemblyTransport

/-! # Canonical Ordinary -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOrdinary.Construction

noncomputable section

/-! The multiplicative/annihilator kernel for the actual canonical source
pairing is the relative Frobenius kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] [CharP k q] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
variable (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable (d r : Fin s → ℕ)
variable (e : ∀ v, OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) 1) q 1 (d v) (r v))

def canonicalOrdinaryPairedFamily (v : Fin s) : OrdinaryFrobenius.Construction.NativeOrdinaryPairedBlock q k :=
  CanonicalIntrinsicPairing.Construction.canonicalNativeOrdinaryPair j iota hsplit A ρ hρ hgood
    (labels (v, false)) (labels (v, true)) (hc v) (e v)

def canonicalOrdinaryFullSplitting : Assembly.Construction.torsionGroup A.abelian q ≅
    BlockProducts.Construction.groupBlockProduct s (fun v =>
      (canonicalOrdinaryPairedFamily j iota hsplit A ρ hρ hgood s labels hc d r e v).chosen ⊗
      (canonicalOrdinaryPairedFamily j iota hsplit A ρ hρ hgood s labels hc d r e v).opposite) :=
  eqToIso (congrArg (Assembly.Construction.torsionGroup A.abelian) (pow_one q).symm) ≪≫
    CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit A.abelian ρ 1 s labels

theorem canonicalOrdinaryFullKernel_frobenius :
    Prescribed.Construction.PrescribedKernel (Torsion.Construction.geometricFrobeniusIsogeny q k A.abelian).hom
      (Canonical.Construction.canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood 1 s labels hc
        (fun v => CMPointsAt.Construction.l45BlockCoordinates j iota hsplit A ρ (labels (v, false)) (e v))
        (fun v => FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e v))) := by
  have h := OrdinaryFrobenius.Construction.fullOrdinaryPaired_frobeniusKernel q k A.abelian s
    (canonicalOrdinaryPairedFamily j iota hsplit A ρ hρ hgood s labels hc d r e)
    (canonicalOrdinaryFullSplitting j iota hsplit A ρ hρ hgood s labels hc d r e)
  have hi : OrdinaryFrobenius.Construction.fullOrdinaryPairedKernelToAbelian q k A.abelian s
      (canonicalOrdinaryPairedFamily j iota hsplit A ρ hρ hgood s labels hc d r e)
      (canonicalOrdinaryFullSplitting j iota hsplit A ρ hρ hgood s labels hc d r e) =
      Canonical.Construction.canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood 1 s labels hc
        (fun v => CMPointsAt.Construction.l45BlockCoordinates j iota hsplit A ρ (labels (v, false)) (e v))
        (fun v => FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e v)) :=
    AssemblyTransport.Construction.fullKernelToAbelian_changeLevel A.abelian (pow_one q).symm s _ _ _
      (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit A.abelian ρ 1 s labels)
  exact hi ▸ h

include hρ hgood hc in
theorem canonicalOrdinaryPrescription_frobenius (T : Over (Spec (.of k)))
    (a : T ⟶ A.abelian.scheme) :
    Prescription.Construction.prescribedFullKernel j iota hsplit A ρ 1 s labels
      (fun v => FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (e v)) T a ↔
      a ≫ (Torsion.Construction.geometricFrobeniusIsogeny q k A.abelian).hom = 1 := by
  rw [← CanonicalPoints.Construction.canonicalFullKernel_realizes j iota hsplit A ρ hρ hgood 1 s labels hc
    (fun v => CMPointsAt.Construction.l45BlockCoordinates j iota hsplit A ρ (labels (v, false)) (e v))]
  have h := canonicalOrdinaryFullKernel_frobenius j iota hsplit A ρ hρ hgood s labels hc d r e T a
  constructor
  · rintro ⟨z, hz⟩
    apply h.mpr
    refine ⟨z, hz, fun z' hz' => ?_⟩
    exact (cancel_mono _).mp (hz'.trans hz.symm)
  · intro ha
    exact (h.mp ha).exists

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalOrdinary.Construction
