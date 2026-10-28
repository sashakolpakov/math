import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ResiduePoint
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint

/-! # Reduction Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM

noncomputable section

/-! Identify CMPoints's actual geometric-fiber points with the prime-field
geometric points used for the native FrobeniusKernel kernel constructions. The
ordinary predicates agree because their full torsion groups agree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM

def pullbackTorsionEquiv {S T U V : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : T ⟶ S) (h : U ⟶ S)
    (x : V ⟶ T) (y : V ⟶ U) (he : x ≫ f = y ≫ h) (n : ℕ) :
    (A.pullback f).torsionPoints n (Over.mk x) ≃*
      (A.pullback h).torsionPoints n (Over.mk y) := by
  let e : (Over.map h).obj (Over.mk y) ≅ (Over.map f).obj (Over.mk x) :=
    Over.isoMk (Iso.refl V) (by
      change (𝟙 V) ≫ (x ≫ f) = y ≫ h
      exact (Category.id_comp _).trans he)
  exact (A.torsionBaseChangeEquiv f (Over.mk x) n).trans
    ((CategoryTheory.Iso.groupIsoToMulEquiv ((A.torsionFunctor n).mapIso e.op)).trans
      (A.torsionBaseChangeEquiv h (Over.mk y) n).symm)

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

abbrev k := AlgebraicClosure (ZMod q)

def primeFieldPoint (p : Geometric.PointExt.CM.pointBase (k (q := q)) ⟶ R.geometricFiber a) :
    AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a := by
  let z : Spec (.of (k (q := q))) ⟶ pullback (M.integral a).toOver.hom R.geometricBase := p.left
  have hz : z ≫ pullback.snd (M.integral a).toOver.hom R.geometricBase = 𝟙 _ := p.w
  have hb : (z ≫ pullback.fst (M.integral a).toOver.hom R.geometricBase) ≫
      (M.integral a).toOver.hom =
        Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (k (q := q)))) ≫ R.specialBase := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hz, Category.id_comp]
    change Spec.map (CommRingCat.ofHom ((algebraMap (ZMod q) (k (q := q))).comp R.residue)) =
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (k (q := q)))) ≫
        Spec.map (CommRingCat.ofHom R.residue)
    rw [← Spec.map_comp]
    rfl
  exact Over.homMk
    (pullback.lift (z ≫ pullback.fst (M.integral a).toOver.hom R.geometricBase)
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (k (q := q))))) hb)
    (pullback.lift_snd _ _ _)

theorem primeFieldPoint_projection (p : Geometric.PointExt.CM.pointBase (k (q := q)) ⟶ R.geometricFiber a) :
    (primeFieldPoint R a p).left ≫ pullback.fst (M.integral a).toOver.hom R.specialBase =
      p.left ≫ R.projection a := pullback.lift_fst _ _ _

def primeFieldAbelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * M.s) (R.specialFiber a).left :=
  (M.integral a).universal.data.polarized.abelian.pullback
    (pullback.fst (M.integral a).toOver.hom R.specialBase)

def geometricTorsionEquiv (p : Geometric.PointExt.CM.pointBase (k (q := q)) ⟶ R.geometricFiber a) (n : ℕ) :
    (R.abelian a).torsionPoints n (Over.mk p.left) ≃*
      (primeFieldAbelian R a).torsionPoints n (Over.mk (primeFieldPoint R a p).left) :=
  pullbackTorsionEquiv (M.integral a).universal.data.polarized.abelian
    (R.projection a) (pullback.fst (M.integral a).toOver.hom R.specialBase)
    p.left (primeFieldPoint R a p).left (primeFieldPoint_projection R a p).symm n

theorem isOrdinary_iff_primeFieldPoint_count (hs : Smooth (M.integral a).toOver.hom)
    (p : Geometric.PointExt.CM.pointBase (k (q := q)) ⟶ R.geometricFiber a) :
    R.IsOrdinary a (p.left (IsLocalRing.closedPoint (k (q := q)))) ↔
      Nat.card ((primeFieldAbelian R a).torsionPoints q (Over.mk (primeFieldPoint R a p).left)) =
        q ^ (3 * M.s) := by
  let : Smooth (M.integral a).toOver.hom := hs
  let : Smooth (R.geometricFiber a).hom := inferInstanceAs
    (Smooth (pullback.snd (M.integral a).toOver.hom R.geometricBase))
  have hc := Nat.card_congr (geometricTorsionEquiv R a p q).toEquiv
  exact (Geometric.ResiduePoint.CM.RationalOrdinary.isOrdinaryAt_iff_point_count
    (R.geometricFiber a) (R.abelian a) p q).trans (by rw [hc])

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
