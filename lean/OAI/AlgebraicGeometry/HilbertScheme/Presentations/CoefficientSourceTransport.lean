import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientTests

/-! # Coefficient Source Transport -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientSourceTransport

noncomputable section

/-! Coefficient ideals transport across an isomorphism of the source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineIdealCoefficient_transport_source (R : CommRingCat.{u})
    {X Y : Scheme.{u}} (e : Y ≅ X) (f : X ⟶ Spec R) (K : X.IdealSheafData)
    (I : Ideal R) (hI : Affine.IdealCoefficientTests.IsAffineIdealCoefficient R (e.hom ≫ f) (K.comap e.hom) I) :
    Affine.IdealCoefficientTests.IsAffineIdealCoefficient R f K I := by
  intro J
  constructor
  · intro h
    apply (hI J).mp
    rw [Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono e.hom h
  · intro h
    have hj := (hI J).mpr h
    have he := Scheme.IdealSheafData.comap_mono e.inv hj
    dsimp only at he
    simpa only [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Scheme.IdealSheafData.comap_id] using he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientSourceTransport
