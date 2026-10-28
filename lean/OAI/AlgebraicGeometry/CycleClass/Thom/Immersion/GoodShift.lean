import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity

/-! # Good Shift -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GoodShift.Constructions.Construction

noncomputable section

/-! The actual supported sheaf complex of a closed complex immersion,
shifted to its first and only cohomology degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

abbrev regularThomGoodShiftSheafComplex := Z.regularThomSheafComplex.truncGE' (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2*p))

def regularThomGoodShift_zeroHomologyIso :
    (regularThomGoodShiftSheafComplex Z).homology 0 ≅ Z.regularThomSheafComplex.homology (2*p) :=
  HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso Z.regularThomSheafComplex (2*p) 0

theorem regularThomGoodShift_positive_homology_isZero (n : ℕ) (hn : 0<n) :
    IsZero ((regularThomGoodShiftSheafComplex Z).homology n) :=
  (SheafPurity.Constructions.Construction.regularThomSheaf_homology_isZero_except Z (2*p+n) (by omega)).of_iso
    (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodShiftHomologyIso Z.regularThomSheafComplex (2*p) n)

theorem regularThomGoodTruncation_quasiIso :
    QuasiIso (Z.regularThomSheafComplex.πTruncGE (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding (2*p))) :=
  HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.cochainGoodTruncation_quasiIso Z.regularThomSheafComplex (2*p)
    (fun n hn => SheafPurity.Constructions.Construction.regularThomSheaf_exactAt_except Z n (by omega))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GoodShift.Constructions.Construction
