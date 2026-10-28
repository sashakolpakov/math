import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Iterated Carrier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.IteratedCarrier

noncomputable section

/-! Explicit carrier and level conversions between iterated abelian
pullback and the abelian part of iterated polarized pullback. The
heterogeneous level equalities keep the record conversions explicit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

variable {S T U : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S) (h : U ⟶ T)
    {X : HilbertConstruction.Abelian.Schemes.AbelianScheme g U}

def polarizedIteratedCarrierIso
    (e : X.scheme ≅ ((A.abelian.pullback f).pullback h).scheme) :
    X.scheme ≅ ((A.pullback f).pullback h).abelian.scheme := by
  dsimp only [HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pullback]
  exact e

theorem polarizedIteratedCarrierIso_isMonHom
    (e : X.scheme ≅ ((A.abelian.pullback f).pullback h).scheme) [hm : IsMonHom e.hom] :
    IsMonHom (polarizedIteratedCarrierIso A f h e).hom := by
  dsimp only [polarizedIteratedCarrierIso, HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pullback]
  exact hm

theorem polarizedIteratedCarrierIso_transport_heq
    (e : X.scheme ≅ ((A.abelian.pullback f).pullback h).scheme) [IsMonHom e.hom]
    (α : X.FullLevel N) :
    HEq (α.transport (A := X) (B := (A.abelian.pullback f).pullback h) e)
      (@HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport g N U X ((A.pullback f).pullback h).abelian α
        (polarizedIteratedCarrierIso A f h e) (polarizedIteratedCarrierIso_isMonHom A f h e)) := by
  rfl

theorem polarizedIteratedLevel_heq :
    HEq ((A.pullback f).pullback h).level ((A.level.pullback f).pullback h) := by
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.IteratedCarrier
