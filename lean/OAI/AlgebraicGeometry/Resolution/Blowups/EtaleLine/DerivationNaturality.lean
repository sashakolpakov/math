import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.HypersurfaceCenters
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations

/-! # Derivation Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.DerivationNaturality.Construction

noncomputable section

/-! The normal derivative is preserved when a relative line chart is refined. -/

open _root_.Polynomial

variable {H R V : Type*} [CommRing H] [CommRing R] [CommRing V]
  [Algebra H R] [Algebra H V] [Algebra R V] [IsScalarTower H R V]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.FormallyEtale H[X] R]
  [Algebra H[X] V] [IsScalarTower H[X] R V] [IsScalarTower H H[X] V]

/-- A normal derivative on any refinement agrees on the old chart with its
old normal derivative. Étale uniqueness only uses the old coordinate map. -/
theorem etaleLine_normalDerivation_natural (D : Derivation H V V)
    (hD : D (algebraMap R V (algebraMap H[X] R X)) = 1) (x : R) :
    D (algebraMap R V x) =
      algebraMap R V (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R) x) := by
  let E : Derivation H R V := (Algebra.linearMap R V).compDer
    (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R))
  have hP : (D.compAlgebraMap R).compAlgebraMap H[X] = E.compAlgebraMap H[X] := by
    apply Polynomial.derivation_ext
    change D (algebraMap R V (algebraMap H[X] R X)) =
      algebraMap R V (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R) (algebraMap H[X] R X))
    rw [hD, Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate, map_one]
  have hE : D.compAlgebraMap R = E := by
    apply Etale.ModuleDerivations.Construction.etaleModuleDerivation_ext (A := H[X])
    intro p
    exact Derivation.congr_fun hP p
  exact Derivation.congr_fun hE x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.DerivationNaturality.Construction
