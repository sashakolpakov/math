import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.HomFieldDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.DualProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.HomOpenCoverDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointEquivalence

/-! # Polarized Dual Hom Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Field pullbacks detect homomorphisms from a polarized abelian family
to its dual over every locally Noetherian base. The required product
embeddings are constructed on affine opens. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i)

include hδ

set_option backward.isDefEq.respectTransparency false in
theorem PolarizationData.PolarizedAbelianWithFullLevel.dualHom_eq_of_fieldPullbacks
    (f q : A.abelian.scheme ⟶ A.dual.abelian.scheme) [IsMonHom f] [IsMonHom q]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ S),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let C := S.affineOpenCover.openCover
  apply HilbertConstruction.Over.HomOpenCoverDetection.overHom_eq_of_openCoverPullbacks C
  intro i
  let R := S.affineOpenCover.X i
  let : IsNoetherianRing R := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian S i
  let : IsAffine (C.X i) := inferInstanceAs (IsAffine (Spec R))
  let : IsNoetherian (C.X i) := inferInstanceAs (IsNoetherian (Spec R))
  let : IsNoetherianRing Γ(C.X i, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let B := A.pullback (C.f i)
  let P := B.projectivePresentation_of_noetherian_affine
  let Q := B.dualProjectivePresentation_of_noetherian_affine hδ
  apply Embedded.HomFieldDetection.embeddedAbelianHom_eq_of_fieldPullbacks B.abelian B.dual.abelian
    (P.product Q).embedding ((Over.pullback (C.f i)).map f) ((Over.pullback (C.f i)).map q)
  intro K _ s
  exact (Iterated.PullbackMapEquality.overPullback_map_eq_iff_iterated s (C.f i) f q).mp (h K (s ≫ C.f i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
