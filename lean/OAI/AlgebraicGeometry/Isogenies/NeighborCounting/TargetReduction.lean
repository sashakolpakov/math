import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.TorsionTower

/-! # Target Reduction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TargetReduction

noncomputable section

/-!
Identify the reduction of an actual generic neighbor target with the
quotient by its integral closed kernel. The generic quotient comparison
is constructed by descent and extended by HomExtension. Specialization is then
the genuine base change of the quotient isomorphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {d : ℕ} {A Q B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of R))}

/-- A good model of the generic neighbor agrees with the integral quotient
when the generic kernels agree. The comparison is constructed, not supplied. -/
def goodTargetComparison
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (IntegralComparison.genericMap (K := K)))
      (B.pullback (IntegralComparison.genericMap (K := K))))
    (hgenericKernel : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := K))) g) :
    Q.scheme ≅ B.scheme :=
  IntegralComparison.extendIso Q B (QuotientComparison.quotientIso (p.pullback (IntegralComparison.genericMap (K := K))) g hgenericKernel)

instance goodTargetComparison_isMonHom
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (IntegralComparison.genericMap (K := K)))
      (B.pullback (IntegralComparison.genericMap (K := K))))
    (hgenericKernel : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := K))) g) :
    IsMonHom (goodTargetComparison p g hgenericKernel).hom :=
  inferInstanceAs (IsMonHom
    (IntegralComparison.extendIso Q B (QuotientComparison.quotientIso (p.pullback (IntegralComparison.genericMap (K := K))) g hgenericKernel)).hom)

local instance goodTargetComparison_left_isIso
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (IntegralComparison.genericMap (K := K)))
      (B.pullback (IntegralComparison.genericMap (K := K))))
    (hgenericKernel : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := K))) g) :
    IsIso (goodTargetComparison p g hgenericKernel).hom.left :=
  inferInstanceAs (IsIso ((Over.forget (Spec (.of R))).map
    (goodTargetComparison p g hgenericKernel).hom))

theorem goodTargetComparison_generic_projection
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (IntegralComparison.genericMap (K := K)))
      (B.pullback (IntegralComparison.genericMap (K := K))))
    (hgenericKernel : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := K))) g) :
    (Over.pullback (IntegralComparison.genericMap (K := K))).map
      (p.hom ≫ (goodTargetComparison p g hgenericKernel).hom) = g.hom := by
  rw [Functor.map_comp]
  change (p.pullback (IntegralComparison.genericMap (K := K))).hom ≫
    (Over.pullback (IntegralComparison.genericMap (K := K))).map
      (IntegralComparison.extendHom Q B (QuotientComparison.quotientIso (p.pullback (IntegralComparison.genericMap (K := K))) g hgenericKernel).hom) = _
  rw [IntegralComparison.extendHom_generic]
  exact QuotientComparison.quotientIso_projection _ _ _

/-- The Neron extension of the generic neighbor map is an isogeny:
it is the constructed finite flat quotient followed by an integral isomorphism. -/
def extendedNeighborIsogeny
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (IntegralComparison.genericMap (K := K)))
      (B.pullback (IntegralComparison.genericMap (K := K))))
    (hgenericKernel : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := K))) g) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B where
  hom := p.hom ≫ (goodTargetComparison p g hgenericKernel).hom
  preservesGroup := inferInstance
  finite := inferInstanceAs
    (IsFinite (p.hom.left ≫ (goodTargetComparison p g hgenericKernel).hom.left))
  flat := inferInstanceAs
    (Flat (p.hom.left ≫ (goodTargetComparison p g hgenericKernel).hom.left))
  surjective := inferInstanceAs
    (Surjective (p.hom.left ≫ (goodTargetComparison p g hgenericKernel).hom.left))

theorem extendedNeighborIsogeny_eq_neron
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (IntegralComparison.genericMap (K := K)))
      (B.pullback (IntegralComparison.genericMap (K := K))))
    (hgenericKernel : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := K))) g) :
    (extendedNeighborIsogeny p g hgenericKernel).hom = IntegralComparison.extendHom A B g.hom := by
  apply AbelianScheme.HomExtension.generic_fiber_map_injective (K := K) A.scheme B.scheme
  exact (goodTargetComparison_generic_projection p g hgenericKernel).trans
    (IntegralComparison.extendHom_generic A B g.hom).symm

/-- The reduced target of the independently evaluated generic neighbor
is the quotient by the actual specialized closed subgroup scheme. -/
theorem goodTarget_reduction_is_kernel_quotient
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q) [LocallyOfFinitePresentation p.hom.left]
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (IntegralComparison.genericMap (K := K)))
      (B.pullback (IntegralComparison.genericMap (K := K))))
    (hgenericKernel : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := K))) g)
    {H : Over (Spec (.of R))} (i : H ⟶ A.scheme) [Mono i]
    (hkernel : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel p.hom i)
    {T : Scheme.{u}} (s : T ⟶ Spec (.of R)) :
    QuotientGraphs.reducedQuotientTarget s i =
      Quotient.mk _ ((AbelianScheme.FrobeniusKernel.BaseChange.Construction.fppfPoints T).obj (B.pullback s).scheme) := by
  apply Quotient.sound
  exact ⟨(AbelianScheme.FrobeniusKernel.BaseChange.Construction.fppfBaseChange s).mapIso
      (AbelianScheme.FrobeniusKernel.Prescribed.Construction.prescribedFrobeniusQuotientIsoOfHomomorphisms p.hom i hkernel
        (Picard.Homomorphisms.Quotient.Construction.isFppfQuotientByKernel_of_fppf p.hom) ≪≫
        (AbelianScheme.FrobeniusKernel.BaseChange.Construction.fppfPoints _).mapIso (goodTargetComparison p g hgenericKernel)) ≪≫
    AbelianScheme.FrobeniusKernel.BaseChange.Construction.fppfBaseChangePointsIso s B.scheme⟩

/-- Ordinary source torsion supplies division of every kernel point.
Thus the actual reduced neighbor has the same maximal q-rank. -/
theorem goodTarget_is_ordinary
    (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A Q)
    (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback (IntegralComparison.genericMap (K := K)))
      (B.pullback (IntegralComparison.genericMap (K := K))))
    (hgenericKernel : QuotientComparison.SameKernel (p.pullback (IntegralComparison.genericMap (K := K))) g)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of R))
    (q i : ℕ) (tower : AbelianScheme.FrobeniusKernel.TorsionTower.Construction.GeometricEtaleTorsionTower (A.Points (Over.mk s)) q d)
    (hkernel : ∀ (T : Over (Spec (.of R))) (a : T ⟶ A.scheme),
      a ≫ p.hom = 1 → a ^ (q ^ i) = 1)
    (hordinary : Nat.card (A.torsionPoints q (Over.mk s)) = q ^ d) :
    Nat.card (B.torsionPoints q (Over.mk s)) = q ^ d := by
  let f := extendedNeighborIsogeny p g hgenericKernel
  have hk (x : f.kernelAt (Over.mk s)) : x.val ^ (q ^ i) = 1 := by
    apply hkernel (Over.mk s) x.val
    apply (cancel_mono (goodTargetComparison p g hgenericKernel).hom).mp
    rw [MonObj.one_comp]
    change (x.val ≫ p.hom) ≫ (goodTargetComparison p g hgenericKernel).hom = 1
    exact (Category.assoc _ _ _).trans x.property
  exact (AbelianScheme.FrobeniusKernel.TorsionTower.Construction.isogeny_qRank_preserved_of_ordinary_tower f s q i d tower hk).symm.trans hordinary

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TargetReduction
