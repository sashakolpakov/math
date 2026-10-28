import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualFiberSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineSchemeModels

/-! # Affine Dual Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualProduct

noncomputable section

/-! An arbitrary smooth affine family over dual numbers is a product
of its actual scheme-theoretic special fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [CommRing k]

def dualBaseProjection : Spec (.of (DualNumber k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))

def dualBaseReduction : Spec (.of k) ⟶ Spec (.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

attribute [local implicit_reducible] dualBaseProjection dualBaseReduction

def canonicalDualFiberIso (S : Type) [CommRing S]
    [Algebra (DualNumber k) S] [Algebra k S] [IsScalarTower k (DualNumber k) S] :
    EtaleSplittingAt.EtaleSplitting.affineOver k (CanonicalDualSpecialFiber.dualSpecialFiber k S) ≅
      (Over.pullback (dualBaseReduction k)).obj (EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) S) :=
  Over.isoMk (CanonicalDualFiberSquare.canonical_dual_specialFiber_isPullback k S).isoPullback
    (CanonicalDualFiberSquare.canonical_dual_specialFiber_isPullback k S).isoPullback_hom_snd

theorem exists_smooth_affine_dual_family_product
    (X : Over (Spec (.of (DualNumber k)))) [IsAffine X.left] [Smooth X.hom] :
    Nonempty (X ≅ (Over.pullback (dualBaseProjection k)).obj
      ((Over.pullback (dualBaseReduction k)).obj X)) := by
  let S := HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra (DualNumber k) X
  let : Algebra k S :=
    ((algebraMap (DualNumber k) S).comp (algebraMap k (DualNumber k))).toAlgebra
  let : IsScalarTower k (DualNumber k) S :=
    IsScalarTower.of_algebraMap_eq' (R := k) (S := DualNumber k) (A := S) rfl
  have : Algebra.Smooth (DualNumber k) S := HilbertConstruction.Smooth.AffineSchemeModels.affineOverAlgebra_smooth (DualNumber k) X
  obtain ⟨e, _⟩ := DualReductionTrivialization.exists_smooth_dual_affine_product_from_reduction
    (Ideal.Quotient.mk (CanonicalDualSpecialFiber.dualSpecialFiberIdeal k S)) Ideal.Quotient.mk_surjective
    Ideal.mk_ker (CanonicalDualSpecialFiber.dualSpecialFiber_quotient_base k S)
  let f : X ≅ EtaleSplittingAt.EtaleSplitting.affineOver (DualNumber k) S := HilbertConstruction.Affine.OverChartPoints.affineOverIso (DualNumber k) X
  let a := canonicalDualFiberIso k S ≪≫ (Over.pullback (dualBaseReduction k)).mapIso f.symm
  exact ⟨f ≪≫ e ≪≫ (Over.pullback (dualBaseProjection k)).mapIso a⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.AffineDualProduct
