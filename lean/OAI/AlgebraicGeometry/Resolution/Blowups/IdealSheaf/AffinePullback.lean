import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.ProductPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.ComponentGluing

/-! # Affine Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.AffinePullback.Construction

noncomputable section

/-! Actual affine ideals of a pulled-back ideal sheaf on subordinate affine neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem idealSheaf_comap_ideal_of_le {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    (U : X.affineOpens) (V : Y.affineOpens) (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U.1 V.1 h).hom := by
  apply (GlobalCoefficient.ComponentGluing.Construction.affineQuotientKernel_eq_iff _ _).mp
  calc
    Affine.QuotientKernel.Construction.affineQuotientKernel ((I.comap f).ideal V) = (I.comap f).comap V.2.fromSpec :=
      (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel (I.comap f) V).symm
    _ = I.comap (Spec.map (f.appLE U.1 V.1 h) ≫ U.2.fromSpec) := by
      rw [← Scheme.IdealSheafData.comap_comp, IsAffineOpen.SpecMap_appLE_fromSpec f U.2 V.2 h]
    _ = Affine.QuotientKernel.Construction.affineQuotientKernel ((I.ideal U).map (f.appLE U.1 V.1 h).hom) :=
      Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel I U (f.appLE U.1 V.1 h).hom

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.AffinePullback.Construction
