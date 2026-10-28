import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialUnitGluing

/-! # Equality Gluing -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing.Construction

noncomputable section

/-! Exact ideal sheaf comparisons descend from native open covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A native open cover detects containment of locally Noetherian ideal sheaves. -/
theorem idealSheaf_le_of_openCover {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (C : X.OpenCover)
    (h : ∀ i, I.comap (C.f i) ≤ J.comap (C.f i)) : I ≤ J := by
  apply (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_eq_top_iff J I).mp
  apply DifferentialUnitGluing.Construction.idealSheaf_eq_top_of_openCover _ C
  intro i
  let : IsLocallyNoetherian (C.X i) := LocallyOfFiniteType.isLocallyNoetherian (C.f i)
  rw [ColonRestriction.Construction.noetherianIdealSheafColon_comap_open]
  exact (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon_eq_top_iff _ _).mpr (h i)

/-- Equality of actual pulled-back ideal sheaves on a native open cover
implies equality of the original sheaves. -/
theorem idealSheaf_eq_of_openCover {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (C : X.OpenCover)
    (h : ∀ i, I.comap (C.f i) = J.comap (C.f i)) : I = J := by
  exact le_antisymm (idealSheaf_le_of_openCover I J C (fun i => (h i).le))
    (idealSheaf_le_of_openCover J I C (fun i => (h i).ge))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.EqualityGluing.Construction
