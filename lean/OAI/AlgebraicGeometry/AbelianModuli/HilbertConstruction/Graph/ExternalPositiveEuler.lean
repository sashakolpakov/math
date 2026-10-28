import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompactExternalAcyclicEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldEulerFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorAmpleness

/-! # External Positive Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The external product of positive canonical graph powers has its exact
Euler monomial, over every field satisfying the original tame-level condition. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_external_positivePowers_euler
    (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic
      (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom)
      (Line.Bundles.LineBundle.externalTensor A.abelian.scheme.hom A.abelian.scheme.hom
        (A.graphBundle.tensorPower m) (A.graphBundle.tensorPower n)).sheaf =
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf) ^ 2 *
      (m : ℤ) ^ g * (n : ℤ) ^ g := by
  let f := A.abelian.scheme.hom
  have : IsProper f := A.abelian.proper
  have : A.abelian.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from f]
    infer_instance
  have : CompactSpace A.abelian.scheme.left := QuasiCompact.compactSpace_of_compactSpace f
  have : IsProper (pullback.fst f f ≫ f) := inferInstance
  have : (CategoryTheory.Limits.pullback f f).IsSeparated := by
    constructor
    rw [← terminal.comp_from (pullback.fst f f ≫ f)]
    infer_instance
  have hunit : IsUnit (N : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of k))))
  have hL (q : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (A.graphBundle.tensorPower m).sheaf (q + 1)) :=
    ModuleCat.subsingleton_of_isZero
      (A.graphBundle_positivePower_cohomology_vanishes_overField hN hunit m hm q)
  have hM (q : ℕ) : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (A.graphBundle.tensorPower n).sheaf (q + 1)) :=
    ModuleCat.subsingleton_of_isZero
      (A.graphBundle_positivePower_cohomology_vanishes_overField hN hunit n hn q)
  have hE := CompactExternalAcyclicEuler.fieldExternal_euler_of_positive_vanishing_of_compact
    (IsPullback.of_hasPullback f f) (A.graphBundle.tensorPower m) (A.graphBundle.tensorPower n) hL hM
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic (pullback.fst f f ≫ f)
      (Line.Bundles.LineBundle.externalTensor f f (A.graphBundle.tensorPower m) (A.graphBundle.tensorPower n)).sheaf = _
  rw [pullback.condition]
  erw [hE, A.graphBundle_positivePower_euler_overField hN hNk m hm,
    A.graphBundle_positivePower_euler_overField hN hNk n hn]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
