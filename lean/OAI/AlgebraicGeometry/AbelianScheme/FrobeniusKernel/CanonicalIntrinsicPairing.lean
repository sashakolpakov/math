import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt

/-! # Canonical Intrinsic Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalIntrinsicPairing.Construction

noncomputable section

/-! The native opposite Cartier map at each level is constructed from the
actual character-line pairing and the original Rosati polarization. -/

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
variable (τ τc : Gal(E/ℚ)) (hτc : τc = PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ) (n : ℕ)

include hτc in
def canonicalPairingAtLevel
    (P : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n)) :
    CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τc n ≅ P.dualGroup := by
  subst τc
  exact CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso j iota hsplit A ρ n τ hρ hgood P

theorem canonicalPairingAtLevel_orthogonal
    (P : CartierModel.Construction.CartierCoordinates (.of k) (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n))
    (T : Over (Spec (.of k))) (x : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X)
    (y : T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τc n).X) :
    ((P.pointsEquiv T (y ≫ (canonicalPairingAtLevel j iota hsplit A ρ hρ hgood τ τc hτc n P).hom.hom.hom)).app
      (.op (Over.mk (𝟙 T)))) x = 1 ↔
      Prescription.Construction.canonicalTorsionOrthogonal A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) T
        (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T x)
        (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τc T y) := by
  subst τc
  exact CanonicalBlockComponents.Construction.canonicalSheafCartierGroupIso_orthogonal j iota hsplit A ρ n τ hρ hgood P T x y

def canonicalNativeOrdinaryPair {d r : ℕ}
    (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ 1) q 1 d r) :
    OrdinaryFrobenius.Construction.NativeOrdinaryPairedBlock q k where
  chosen := CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ 1
  opposite := CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τc 1
  multiplicativeHeight := d
  etaleHeight := r
  splitting := e
  coordinates := CMPointsAt.Construction.l45BlockCoordinates j iota hsplit A ρ τ e
  pairing := canonicalPairingAtLevel j iota hsplit A ρ hρ hgood τ τc hτc 1 _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalIntrinsicPairing.Construction
