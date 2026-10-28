import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualNormalizedTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyNormalizedPullback

/-! # Dual Transport Naturality -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualTransportNaturality

noncomputable section

/-! The quotient-dual normalized comparisons commute with arbitrary
maps between quasi-compact, quasi-separated parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyNormalizedPullback.Construction (familyIsoPullback familyIsoPullback_normalized)

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable {T U : Over (Spec (.of k))}
variable [CompactSpace T.left] [QuasiSeparatedSpace T.left] [CompactSpace U.left] [QuasiSeparatedSpace U.left]
variable (a b : T ⟶ D.abelian.scheme)
variable (hab : a ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection = b ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection)

theorem quotientDualNormalizedIso_pullback (t : U ⟶ T) (a' b' : U ⟶ D.abelian.scheme)
    (hta : t ≫ a = a') (htb : t ≫ b = b')
    (hab' : a' ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection = b' ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection) :
    AbelianScheme.FrobeniusKernel.FamilyNormalizedPullback.Construction.familyIsoPullback B a (DualSheaf.quotientDualSourcePoincare D f) b
        (DualNormalizedTransport.quotientDualNormalizedIso D f r T a b hab) t a' b' hta htb =
      DualNormalizedTransport.quotientDualNormalizedIso D f r U a' b' hab' := by
  apply DualNormalizedTransport.quotientDualPoincareIso_ext D f U a' b'
  · exact AbelianScheme.FrobeniusKernel.FamilyNormalizedPullback.Construction.familyIsoPullback_normalized B a (DualSheaf.quotientDualSourcePoincare D f)
      (DualSheaf.quotientDualSourcePoincare_normalized D f).some b
      (DualNormalizedTransport.quotientDualNormalizedIso D f r T a b hab) t a' b' hta htb
      (DualNormalizedTransport.quotientDualNormalizedIso_zero D f r T a b hab)
  · exact DualNormalizedTransport.quotientDualNormalizedIso_zero D f r U a' b' hab'

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualTransportNaturality
