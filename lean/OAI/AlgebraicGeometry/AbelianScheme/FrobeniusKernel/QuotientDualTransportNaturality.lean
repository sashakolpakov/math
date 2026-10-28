import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualNormalizedTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyNormalizedPullback

/-! # Quotient Dual Transport Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualTransportNaturality.Construction

noncomputable section

/-! The quotient-dual normalized comparisons commute with arbitrary
maps between quasi-compact, quasi-separated parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable {T U : Over (Spec (.of k))}
variable [CompactSpace T.left] [QuasiSeparatedSpace T.left] [CompactSpace U.left] [QuasiSeparatedSpace U.left]
variable (a b : T ⟶ D.abelian.scheme)
variable (hab : a ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection = b ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection)

theorem quotientDualNormalizedIso_pullback (t : U ⟶ T) (a' b' : U ⟶ D.abelian.scheme)
    (hta : t ≫ a = a') (htb : t ≫ b = b')
    (hab' : a' ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection = b' ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection) :
    FamilyNormalizedPullback.Construction.familyIsoPullback B a (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f) b
        (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r T a b hab) t a' b' hta htb =
      QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r U a' b' hab' := by
  apply QuotientDualNormalizedTransport.Construction.quotientDualPoincareIso_ext D f U a' b'
  · exact FamilyNormalizedPullback.Construction.familyIsoPullback_normalized B a (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f)
      (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare_normalized D f).some b
      (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso D f r T a b hab) t a' b' hta htb
      (QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso_zero D f r T a b hab)
  · exact QuotientDualNormalizedTransport.Construction.quotientDualNormalizedIso_zero D f r U a' b' hab'

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualTransportNaturality.Construction
