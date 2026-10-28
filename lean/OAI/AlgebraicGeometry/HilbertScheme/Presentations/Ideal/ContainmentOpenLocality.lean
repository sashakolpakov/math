import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.OpenEquality

/-! # Containment Open Locality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentOpenLocality

noncomputable section

/-! Containment of actual ideal sheaves can be checked on any open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
variable {X : Scheme.{u}}

theorem ideal_le_of_openCover (U : X.OpenCover.{v}) (I J : X.IdealSheafData)
    (h : ∀ i, I.comap (U.f i) ≤ J.comap (U.f i)) : I ≤ J := by
  have he : I ⊔ J = J := by
    apply AbelianModuli.HilbertConstruction.ClosedFamily.OpenEquality.ideal_eq_of_open_cover U
    intro i
    rw [Scheme.IdealSheafData.comap_sup, sup_eq_right.mpr (h i)]
  exact sup_eq_right.mp he

theorem ideal_le_iff_openCover (U : X.OpenCover.{v}) (I J : X.IdealSheafData) :
    I ≤ J ↔ ∀ i, I.comap (U.f i) ≤ J.comap (U.f i) :=
  ⟨fun h i => Scheme.IdealSheafData.comap_mono (U.f i) h, ideal_le_of_openCover U I J⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Ideal.ContainmentOpenLocality
