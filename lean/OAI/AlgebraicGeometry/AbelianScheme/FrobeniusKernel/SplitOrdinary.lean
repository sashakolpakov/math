import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Ordinary
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Multiplicative

/-! # Split Ordinary -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitOrdinary.Construction

noncomputable section

/-!
The native μ × etale ordinary splitting gives the exact embedded
Frobenius kernel and the quotient comparison, with no Frobenius-kernel
identification assumed. The quotient projection is compared explicitly.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) {d r : ℕ}
variable (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k (Assembly.Construction.torsionGroup A p) p 1 d r)

instance geometricFrobeniusKernelInclusion_mono :
    Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom) :=
  inferInstanceAs (Mono (CategoryTheory.Limits.equalizer.ι
    (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom (1 : A.scheme ⟶ _)))

omit [IsAlgClosed k] in
theorem geometricFrobenius_isFppfQuotient :
    Picard.Homomorphisms.Quotient.Construction.IsFppfQuotientByKernel (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom :=
  (Picard.Homomorphisms.Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient p (Fact.out : p.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A.scheme).2.2

abbrev splitOrdinaryMultiplicativeKernel :
    (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k p 1 d).X ⟶ A.scheme :=
  Ordinary.Construction.ordinaryFactorToAbelian p k A (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k p 1 d) (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 r) e

theorem splitOrdinary_frobeniusKernel :
    Prescribed.Construction.PrescribedKernel (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom
      (splitOrdinaryMultiplicativeKernel p k A e) := by
  have : Etale (OrdinaryBlocks.Construction.etaleOrdinaryBlock k p 1 r).X.hom := EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  exact Ordinary.Construction.ordinaryFactor_is_frobeniusKernel p k A _ _ e
    (Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius p k d)

/-- Equality is equality of the embedded scheme subobjects of A. -/
theorem splitOrdinary_frobeniusKernel_subobject :
    Subobject.mk (splitOrdinaryMultiplicativeKernel p k A e) =
      Subobject.mk (Picard.Homomorphisms.Kernel.Construction.kernelInclusion (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom) :=
  Subobject.mk_eq_mk_of_comm _ _
    (Prescribed.Construction.prescribedKernelIso (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom _
      (splitOrdinary_frobeniusKernel p k A e))
    (Prescribed.Construction.prescribedKernelIso_inclusion (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom _
      (splitOrdinary_frobeniusKernel p k A e))

/-- The quotient by the independent ordinary multiplicative prescription
is the native Frobenius twist. -/
def splitOrdinaryFrobeniusQuotientIso :
    BaseChange.Construction.subgroupQuotient (splitOrdinaryMultiplicativeKernel p k A e) ≅
      (BaseChange.Construction.fppfPoints (Spec (.of k))).obj
        (A.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p (Fact.out : p.Prime) _
          (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)))).scheme :=
  Prescribed.Construction.prescribedFrobeniusQuotientIsoOfHomomorphisms (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom _
    (splitOrdinary_frobeniusKernel p k A e)
    (geometricFrobenius_isFppfQuotient p k A)

theorem splitOrdinaryFrobeniusQuotientIso_projection :
    Prescribed.Construction.subgroupQuotientProjection (splitOrdinaryMultiplicativeKernel p k A e) ≫
        (splitOrdinaryFrobeniusQuotientIso p k A e).hom =
      (BaseChange.Construction.fppfPoints (Spec (.of k))).map (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom :=
  Prescribed.Construction.prescribedFrobeniusQuotientIsoOfHomomorphisms_projection (Torsion.Construction.geometricFrobeniusIsogeny p k A).hom _
    (splitOrdinary_frobeniusKernel p k A e)
    (geometricFrobenius_isFppfQuotient p k A)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitOrdinary.Construction
