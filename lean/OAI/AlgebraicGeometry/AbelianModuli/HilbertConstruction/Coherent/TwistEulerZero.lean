import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.GlobalGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.SerreVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ModuleZeroCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorCoherence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Twist Euler Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A coherent sheaf whose entire ample-twist Euler sequence vanishes is zero. The proof uses actual positive-twist global generation, Serre vanishing, finite-dimensional cohomology, and the inverse tensor equivalence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem Coherent.TwistEulerZero.proper_coherent_isZero_of_generated_of_acyclic_euler_zero
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hgen : HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators M)
    (hvan : ∀ q, IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) (q + 1)).obj M))
    (hchi : CohomologyEulerCharacteristic.coefficientEulerCharacteristic p M = 0) : IsZero M := by
  have : Module.Finite K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) 0).obj M) := Proper.CoherentCohomology.proper_coherent_cohomologyFinite p M 0
  let e := CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap p) M
  have : Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have hdim : (Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) : ℤ) = 0 :=
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing p M hvan).symm.trans hchi
  have hz : Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) = 0 := Int.ofNat.inj hdim
  have hsections : Subsingleton ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) := Module.finrank_zero_iff.mp hz
  exact HilbertConstruction.Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.isZero_of_sections_subsingleton M hgen hsections

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.coherent_isZero_of_twist_euler_zero
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hzero : ∀ m, CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (Tensor.ProductSheaf.tensorModule M (L.tensorPower m).sheaf) = 0) :
    IsZero M := by
  obtain ⟨Bgen, hgen⟩ := E.tensorPowers_eventually_hasFiniteGlobalGenerators M
  obtain ⟨Bvan, hvan⟩ := E.tensorPowers_eventually_vanish M
  let b := max Bgen Bvan
  let T := Tensor.ProductSheaf.tensorModule M (L.tensorPower (b * E.degree)).sheaf
  have : T.IsQuasicoherent := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_quasicoherent M _
  have : T.IsFiniteType := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_finiteType M _
  have hT : IsZero T := Coherent.TwistEulerZero.proper_coherent_isZero_of_generated_of_acyclic_euler_zero p T
    (hgen b (le_max_left Bgen Bvan)) (hvan b (le_max_right Bgen Bvan)) (hzero (b * E.degree))
  let F := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence (L.tensorPower (b * E.degree))
  have hFM : IsZero (F.functor.obj M) :=
    (LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso (L.tensorPower (b * E.degree)) M).isZero_iff.mpr hT
  exact (F.unitIso.app M).isZero_iff.mpr (F.inverse.map_isZero hFM)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
