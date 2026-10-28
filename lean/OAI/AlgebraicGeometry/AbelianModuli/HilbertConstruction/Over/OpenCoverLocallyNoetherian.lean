import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Open Cover Locally Noetherian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.OpenCoverLocallyNoetherian

/-! Local Noetherianity of an actual open-cover member over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem overOpenCoverObject_locallyNoetherian
    {B : Scheme.{u}} (G : Over B) [hG : IsLocallyNoetherian G.left]
    (C : Scheme.OpenCover.{v} G.left) (i : C.I₀) :
    IsLocallyNoetherian (Embedded.FamilyOpenCover.overOpenCoverObject G C i).left :=
  @isLocallyNoetherian_of_isOpenImmersion (C.X i) G.left (C.f i) (C.map_prop i) hG

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.OpenCoverLocallyNoetherian
