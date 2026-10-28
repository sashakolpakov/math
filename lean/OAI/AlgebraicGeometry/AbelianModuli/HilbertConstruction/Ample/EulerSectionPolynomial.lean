import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.SerreVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.SectionPolynomial

/-! # Euler Section Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! For an ample line bundle on a proper scheme, an Euler polynomial is
the genuine eventual section Hilbert polynomial. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Line.Bundles.LineBundle.hasSectionHilbertPolynomial_of_euler
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (L : Line.Bundles.LineBundle X) (hL : L.IsAmple) (P : Polynomial ℚ)
    (hP : ∀ n : ℕ, P.eval (n : ℚ) = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensorPower n).sheaf : ℚ)) :
    L.HasSectionHilbertPolynomial p P := by
  have : (Line.Bundles.structureModule X).IsFiniteType := (Line.Bundles.LineBundle.trivial X).isFiniteType
  have : (Line.Bundles.structureModule X).IsQuasicoherent := (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  obtain ⟨B, hB⟩ := Ample.SerreVanishing.ample_tensorPowers_eventually_vanish p L hL (Line.Bundles.structureModule X)
  refine ⟨B, fun n hn => ?_⟩
  let M := (L.tensorPower n).sheaf
  have : M.IsFiniteType := (L.tensorPower n).isFiniteType
  have : M.IsQuasicoherent := (L.tensorPower n).isQuasicoherent
  have hzero : ∀ q : ℕ, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) (q + 1)).obj M) := by
    intro q
    exact (hB n hn q).of_iso
      ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap p) (q + 1)).mapIso
        (Tensor.ProductSheaf.tensorModuleUnitLeftIso M)).symm
  have : Module.Finite K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) 0).obj M) := Proper.CoherentCohomology.proper_coherent_cohomologyFinite p M 0
  let e := CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) M
  refine ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, ?_⟩
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing p M hzero)
  exact (hP n).trans (by simpa only [Int.cast_natCast] using h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
