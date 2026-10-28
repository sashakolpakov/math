import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothArithmetic
import OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicIsolatedPoint
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Complex Parameter -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ComplexParameter.Abelian

noncomputable section

/-!
Construct a smooth complex parameter neighborhood of an arbitrary arithmetic
complex point. Its map to the original parameter problem is injective on
actual complex points, and scheme-theoretic isolation in this constructed
neighborhood supplies the already checked number-field descent bridge.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

theorem rational_structure_unique (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (CommRingCat.of ℚ)) :
    p = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) := by
  have h : Spec.preimage p = CommRingCat.ofHom (algebraMap ℚ ℂ) :=
    CommRingCat.hom_ext (Subsingleton.elim _ _)
  exact (Spec.map_preimage p).symm.trans (congrArg Spec.map h)

abbrev arithmeticComplexBase {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of ℚ)) : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))

def arithmeticComplexPoint {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of ℚ))
    (q : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Y) : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (arithmeticComplexBase f) :=
  Over.homMk (pullback.lift q (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (by
    exact (rational_structure_unique (q ≫ f)).trans (Category.id_comp _).symm)) (by
      exact pullback.lift_snd _ _ _)

theorem arithmeticComplexPoint_projection {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of ℚ))
    (q : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Y) :
    (arithmeticComplexPoint f q).left ≫
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) = q := pullback.lift_fst _ _ _

theorem arithmeticComplexBase_pointMap_injective {X Y : Scheme}
    (f : Y ⟶ Spec (CommRingCat.of ℚ)) (i : Y ⟶ X) [Mono i] :
    Function.Injective (fun s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (arithmeticComplexBase f) =>
      s.left ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ≫ i) := by
  intro s t h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply (cancel_mono i).mp
    exact (Category.assoc s.left _ i).trans (h.trans (Category.assoc t.left _ i).symm)
  · exact s.w.trans t.w.symm

/-- The actual smooth complex test parameter and its exact point are
constructed from the arithmetic evaluation kernel. The final implication
is the checked isolation-to-number-field bridge for this parameter. -/
theorem exists_smooth_complex_parameter_with_descent
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType f]
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) :
    ∃ (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (j : S.left ⟶ X) (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S),
      Smooth S.hom ∧ Function.Injective (fun s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S => s.left ≫ j) ∧
      s₀.left ≫ j = p ∧
      (IsOpen {s₀.left (IsLocalRing.closedPoint ℂ)} →
        ∃ (K : Subfield ℂ), NumberField K ∧ ∃ pK : Spec (CommRingCat.of K) ⟶ X,
          Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p) := by
  obtain ⟨Y, g, i, q, _, hg, hi, _, hq⟩ := SmoothArithmetic.Abelian.complex_point_has_smooth_arithmetic_factor f p
  let : Smooth g := hg
  let : Mono i := hi
  let S := arithmeticComplexBase g
  let π : S.left ⟶ Y := pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))
  let j : S.left ⟶ X := π ≫ i
  let s₀ := arithmeticComplexPoint g q
  have hs : s₀.left ≫ j = p := by
    exact (Category.assoc s₀.left π i).symm.trans
      ((congrArg (fun a : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Y => a ≫ i) (arithmeticComplexPoint_projection g q)).trans hq)
  have hS : Smooth S.hom := inferInstanceAs
    (Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))))
  refine ⟨S, j, s₀, hS, arithmeticComplexBase_pointMap_injective g i, hs, ?_⟩
  intro hopen
  obtain ⟨K, hK, qK, hqK⟩ := AlgebraicPoints.Abelian.complex_point_descends_of_isolated_baseChange g s₀.left hopen
  refine ⟨K, hK, qK ≫ i, ?_⟩
  exact (Category.assoc _ qK i).symm.trans
    ((congrArg (fun a : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Y => a ≫ i) hqK).trans
      ((Category.assoc s₀.left π i).trans hs))

theorem exists_smooth_complex_parameter_with_native_descent
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType f]
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) :
    ∃ (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (j : S.left ⟶ X) (s₀ : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S),
      Smooth S.hom ∧ Function.Injective (fun s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S => s.left ≫ j) ∧
      s₀.left ≫ j = p ∧
      (IsOpen ({s₀} : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)) →
        ∃ (K : Subfield ℂ), NumberField K ∧ ∃ pK : Spec (CommRingCat.of K) ⟶ X,
          Spec.map (CommRingCat.ofHom K.subtype) ≫ pK = p) := by
  obtain ⟨S, j, s₀, hS, hinj, hp, hdescent⟩ := exists_smooth_complex_parameter_with_descent f p
  let : Smooth S.hom := hS
  exact ⟨S, j, s₀, hS, hinj, hp, fun hopen => hdescent (IntrinsicIsolatedPoint.Abelian.scheme_isolated_of_native_isolated S s₀ hopen)⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ComplexParameter.Abelian
