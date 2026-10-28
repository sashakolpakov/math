import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalIntrinsicPairing
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedIsogenyOrdinary

/-! # Canonical -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Canonical.Construction

noncomputable section

/-! Embed the full chosen/annihilator product using the explicitly
constructed canonical polarization pairing at every conjugate block.
The quotient and its complete prime-to-q marking are then constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
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

def canonicalFullKernelInclusion :
    (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit A ρ n s labels P H).X ⟶ A.abelian.scheme :=
  PairedKernels.Construction.fullPairedKernelToAbelian A.abelian (q ^ n) s
    (fun v => CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n)
    (fun v => (H v).group)
    (fun v => CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, true)) n)
    P (fun v => (H v).coordinates) (fun v => (H v).inclusion)
    (fun v => CanonicalIntrinsicPairing.Construction.canonicalPairingAtLevel j iota hsplit A ρ hρ hgood
      (labels (v, false)) (labels (v, true)) (hc v) n (P v))
    (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit A.abelian ρ n s labels)

instance canonicalFullKernelInclusion_isMonHom :
    IsMonHom (canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H) :=
  PairedKernels.Construction.fullPairedKernelToAbelian_isMonHom A.abelian (q ^ n) s _ _ _ P _ _ _ _

instance canonicalFullKernelInclusion_closed :
    IsClosedImmersion (canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H).left :=
  PairedKernels.Construction.fullPairedKernelToAbelian_closed A.abelian (q ^ n) s _ _ _ P _ _ _ _ (fun v => (H v).closed)

instance canonicalFullKernelInclusion_mono :
    Mono (canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H) :=
  Over.mono_of_mono_left _

theorem canonicalFullKernel_killed (T : Over (Spec (.of k)))
    (x : T ⟶ (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit A ρ n s labels P H).X) :
    (x ≫ canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H) ^ (q ^ n) = 1 :=
  PairedKernels.Construction.fullPairedKernelToAbelian_killed A.abelian (q ^ n) s _ _ _ P _ _ _ _ T x

def canonicalFullKernelQuotient : GeometricQuotient.Construction.GeometricKernelQuotient A.abelian
    (CMPointsKernels.Construction.l45FullChosenKernel j iota hsplit A ρ n s labels P H)
    (canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H) :=
  GeometricQuotient.Construction.geometricKernelQuotient A.abelian _ _
    (canonicalFullKernelInclusion_closed j iota hsplit A ρ hρ hgood n s labels hc P H)
    (CMPointsKernels.Construction.l45FullChosenKernel_finiteLocallyFree j iota hsplit A ρ n s labels P H)

def canonicalFullQuotientIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.abelian
    (canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).abelian :=
  (canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).isogeny

theorem canonicalFullQuotient_torsionCard (m : ℕ) (hm : 0 < m) :
    Nat.card (A.abelian.torsionPoints m (Over.mk (𝟙 (Spec (.of k))))) =
      Nat.card ((canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).abelian.torsionPoints
        m (Over.mk (𝟙 (Spec (.of k))))) :=
  PolarizedIsogenyOrdinary.Construction.polarizedIsogeny_torsionCard_preserved A.abelian _ A.dual A.polarization.isogeny
    (canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H) m hm

def canonicalFullQuotientLevel (hN : Nat.Coprime q N) :
    (canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).abelian.FullLevel N :=
  (canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).level
    (hN.pow_left n) (canonicalFullKernel_killed j iota hsplit A ρ hρ hgood n s labels hc P H) A.level

theorem canonicalFullQuotientLevel_transports (hN : Nat.Coprime q N)
    (T : (Over (Spec (.of k)))ᵒᵖ)
    (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N (Spec (.of k))).obj T) :
    ((canonicalFullQuotientLevel j iota hsplit A ρ hρ hgood n s labels hc P H hN).hom.app T c).val =
      (A.level.hom.app T c).val ≫
        (canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom :=
  (canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).level_transports
    (hN.pow_left n) (canonicalFullKernel_killed j iota hsplit A ρ hρ hgood n s labels hc P H) A.level T c

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Canonical.Construction
