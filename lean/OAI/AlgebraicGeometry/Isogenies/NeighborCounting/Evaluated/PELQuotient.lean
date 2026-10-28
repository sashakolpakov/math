import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELIsogenySpecialization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TargetReduction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedKernelBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELTargetComparison

/-! # PEL Quotient -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient

noncomputable section

/-! The independent generic PEL target specializes to a full PEL
quotient by the specialized complete integral kernel. The good-model
comparison and every PEL compatibility are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedKernelBaseChange.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TargetReduction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELIsogenySpecialization

variable {R K O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [CommRing O]
variable {d N n : ℕ} {A B : AbelianScheme.TateComparison.PEL.PELFamilyData O d N (Spec (.of R))}
variable {Q : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of R))}
variable (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.abelian Q)
variable (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (A.pullback (IntegralComparison.genericMap (R := R) (K := K)))
  (B.pullback (IntegralComparison.genericMap (R := R) (K := K))) n)
variable (hk : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (R := R) (K := K))) g.isogeny)

theorem extendedNeighbor_sameKernel :
    QuotientComparison.SameKernel p (TargetReduction.extendedNeighborIsogeny p g.isogeny hk) := by
  intro T a
  change a ≫ p.hom = 1 ↔ a ≫ (p.hom ≫ (TargetReduction.goodTargetComparison p g.isogeny hk).hom) = 1
  rw [← Category.assoc, ← MonObj.one_comp (TargetReduction.goodTargetComparison p g.isogeny hk).hom,
    cancel_mono]

theorem extendedNeighbor_prescribedKernel {H : Over (Spec (.of R))}
    (i : H ⟶ A.abelian.scheme) (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (TargetReduction.extendedNeighborIsogeny p g.isogeny hk).hom i :=
  fun T a => ((extendedNeighbor_sameKernel p g hk T a).symm).trans (hi T a)

variable (hnN : Nat.Coprime n N)
variable (hkernel : ∀ (T : Over (Spec (.of R))) (a : T ⟶ A.abelian.scheme),
  a ≫ p.hom = 1 → a ^ n = 1)
variable {k : Type} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of R))

def evaluatedSpecialPELIsogeny : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (A.pullback s) (B.pullback s) n :=
  PELIsogenySpecialization.specialPELIsogeny (TargetReduction.extendedNeighborIsogeny p g.isogeny hk) g
    (TargetReduction.goodTargetComparison_generic_projection p g.isogeny hk) hnN
    (fun T a ha => hkernel T a ((extendedNeighbor_sameKernel p g hk T a).mpr ha)) s

/-- The full special scheme kernel, including every opposite and compact
block present in the original integral subgroup, is preserved exactly. -/
theorem evaluatedSpecialPELIsogeny_kernel {H : Over (Spec (.of R))}
    (i : H ⟶ A.abelian.scheme) (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (evaluatedSpecialPELIsogeny p g hk hnN hkernel s).isogeny.hom
      ((Over.pullback s).map i) :=
  AbelianScheme.FrobeniusKernel.PrescribedKernelBaseChange.Construction.prescribedKernel_baseChange s (TargetReduction.extendedNeighborIsogeny p g.isogeny hk).hom i
    (extendedNeighbor_prescribedKernel p g hk i hi)

/-- An independently constructed PEL quotient of the specialized full
kernel agrees with the reduced generic target in all its PEL data. -/
def independentSpecialPELTargetIso {C : AbelianScheme.TateComparison.PEL.PELFamilyData O d N (Spec (.of k))}
    (h : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (A.pullback s) C n)
    {H : Over (Spec (.of R))} (i : H ⟶ A.abelian.scheme)
    (hi : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i)
    (hh : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel h.isogeny.hom ((Over.pullback s).map i)) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso (B.pullback s) C :=
  PELTargetComparison.quotientPELIso
    (evaluatedSpecialPELIsogeny p g hk hnN hkernel s) h
    (fun T a => (evaluatedSpecialPELIsogeny_kernel p g hk hnN hkernel s i hi T a).trans
      (hh T a).symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELQuotient
