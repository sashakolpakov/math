import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface

/-! # Extended Quotient -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ExtendedQuotient.Construction

noncomputable section

/-! Smooth base change of actual quotient centers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]

/-- The actual quotient by an extended ideal is smooth over the original
quotient when the ambient algebra map is smooth. -/
theorem smooth_quotient_map_of_smooth (I : Ideal R) :
    Algebra.Smooth (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  have hbase : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  have h := MorphismProperty.of_isPullback (P := @Smooth)
    (Affine.QuotientBaseChange.Construction.affineQuotient_baseChange_isPullback (S := S) I).flip hbase
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

variable {k : Type u} [CommRing k] [Algebra k R] [Algebra k S] [IsScalarTower k R S]

/-- Smoothness of the original center over the coefficient ring is retained
under an actual smooth ambient base change. -/
theorem smooth_extended_quotient (I : Ideal R) [Algebra.Smooth k (R ⧸ I)] :
    Algebra.Smooth k (S ⧸ I.map (algebraMap R S)) := by
  let : IsScalarTower k (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I
  let : Algebra.Smooth (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := smooth_quotient_map_of_smooth I
  exact Algebra.Smooth.comp k (R ⧸ I) (S ⧸ I.map (algebraMap R S))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ExtendedQuotient.Construction
