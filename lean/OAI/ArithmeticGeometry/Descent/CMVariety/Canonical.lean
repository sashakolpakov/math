import OAI.AlgebraicGeometry.Albanese.HodgeComparisonIs
import OAI.ArithmeticGeometry.Descent.CMVariety.MarkedActions

/-! # Canonical -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.Canonical.Abelian.IntrinsicPeriods

noncomputable section

/-!
Use the independently constructed canonical weight-one Hodge structure
of the actual projective variety. HodgeComparison's canonical-H¹ construction is
proved, even though its full Albanese comparison target is still open.
No HodgeComparison theorem proposition is added as a hypothesis.
-/

abbrev canonicalH1 (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) := AlgebraicGeometry.Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 A.variety

theorem canonicalH1_isCanonical (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety (canonicalH1 A) := ⟨rfl, rfl⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.Canonical.Abelian.IntrinsicPeriods
