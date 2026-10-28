import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EndomorphismBridge
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.PointedLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ParameterDescent
import OAI.ArithmeticGeometry.Descent.CMVariety.CountableGroupMaps
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons

/-! # Endomorphism Parameter Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EndomorphismParameterDescent

noncomputable section

section

/-! Countability and algebraicity of the actual Presentations endomorphism
parameters for a fixed arithmetic abelian model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem groupEndRing_countable_of_complex_comparison {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (V : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : V.toOver ≅ A.scheme) [IsMonHom e.hom] : Countable (IntegralModel.Finite.Actions.GroupEndRing A) := by
  let : Countable {f : V.toOver ⟶ V.toOver // IsMonHom f} :=
    ArithmeticGeometry.Descent.CMVariety.CountableGroupMaps.Abelian.IntrinsicPeriods.algebraic_group_maps_countable V V
  let encode (f : IntegralModel.Finite.Actions.GroupEndRing A) : {f : V.toOver ⟶ V.toOver // IsMonHom f} :=
    ⟨e.hom ≫ f.hom A ≫ e.inv, inferInstance⟩
  apply Function.Injective.countable (f := encode)
  intro f h heq
  apply IntegralModel.Finite.Actions.GroupEndRing.ext
  apply (cancel_epi e.hom).mp
  apply (cancel_mono e.inv).mp
  exact ((Category.assoc e.hom (f.hom A) e.inv).trans
    (congrArg Subtype.val heq)).trans (Category.assoc e.hom (h.hom A) e.inv).symm

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  {g n : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K)))
  {B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme)}
  {P : Fin n → Polynomial ℚ}
  {L : HilbertScheme.Presentations.Loci.Core.HilbertHomLoci A.scheme A.scheme B n P}
  {R : HilbertScheme.Presentations.Endomorphisms.Core.FiniteEndomorphismEquations A.scheme n}
  (M : HilbertScheme.Presentations.Loci.Core.EndomorphismEquationLoci A.scheme B n P L R)

omit [NumberField K] in
theorem e34_endomorphism_parameters_countable
    [Countable (IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom κ))))] :
    Countable (IntegralModel.CountableParameters.ParameterPoints ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj M.endScheme)) := by
  let T : Over (Spec (.of K)) := Over.mk (Spec.map (CommRingCat.ofHom κ))
  have : Countable (IntegralModel.Finite.Actions.GroupEndRing (A.pullback T.hom)) :=
    inferInstanceAs (Countable (IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom κ)))))
  have : Countable ((HilbertScheme.Presentations.Endomorphisms.Core.endomorphismSubfunctor A.scheme).toFunctor.obj (.op T)) :=
    (IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).symm.injective.countable
  have : Countable ((HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme n).obj (.op T)) :=
    inferInstanceAs (Countable (Fin n → (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismSubfunctor A.scheme).toFunctor.obj (.op T)))
  have : Countable (M.endLocus.toFunctor.obj (.op T)) :=
    inferInstanceAs (Countable {x : (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme n).obj (.op T) //
      x ∈ M.endLocus.obj (.op T)})
  have : Countable (T ⟶ M.endScheme) :=
    ((M.endEquivalence.app (.op T)).toEquiv.injective).countable
  exact (IntegralModel.Arithmetic.PointedLifts.fiberParameterPointsEquiv (Spec.map (CommRingCat.ofHom κ)) M.endScheme).injective.countable

theorem e34_endomorphism_parameter_descends
    (V : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : V.toOver ≅ (A.pullback (Spec.map (CommRingCat.ofHom κ))).scheme) [IsMonHom e.hom]
    (p : Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ M.endScheme) :
    ∃ (F : IntegralModel.Base.ArithmeticBaseExtension K κ) (pF : Over.mk F.fieldExtension ⟶ M.endScheme),
      F.denominator = 1 ∧ F.complexFieldMap ≫ pF = p := by
  let : Countable (IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom κ)))) :=
    groupEndRing_countable_of_complex_comparison _ V e
  let : Countable (IntegralModel.CountableParameters.ParameterPoints ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj M.endScheme)) :=
    e34_endomorphism_parameters_countable κ A M
  let : LocallyOfFiniteType L.homScheme.hom := L.hom_finiteType
  let : IsClosedImmersion M.forgetGroup.left := M.group_closed
  have : LocallyOfFiniteType M.endScheme.hom := by
    rw [← M.forgetGroup.w]
    infer_instance
  let ep := IntegralModel.Arithmetic.PointedLifts.fiberParameterPointsEquiv (Spec.map (CommRingCat.ofHom κ)) M.endScheme
  obtain ⟨F, pF, hF, hpF, heq⟩ := IntegralModel.Arithmetic.Parameters.parameter_finite_extension_of_countable_fiber κ M.endScheme
    (ep.symm p) 1 one_ne_zero
  refine ⟨F, Over.homMk pF hpF, hF, ?_⟩
  apply Over.OverMorphism.ext
  exact heq.trans (congrArg Over.Hom.left (ep.apply_symm_apply p))

end

/-! The ring-valued restriction functor uses the same canonical scheme
comparison as the arithmetic diagram construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies

theorem endomorphism_restrictionIso_eq_iterated {S : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T U : Over S} (b : T ⟶ U) :
    (IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A b).hom =
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.scheme U.hom b.left T.hom b.w).hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso_hom_fst A b).trans
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_fst A.scheme U.hom b.left T.hom b.w).symm
  · exact (IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A b).hom.w.trans
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.scheme U.hom b.left T.hom b.w).hom.w.symm

theorem endomorphism_restrict_compatibility {S : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {T U : Over S} (b : T ⟶ U)
    (r : IntegralModel.Finite.Actions.GroupEndRing (A.pullback U.hom)) (s : IntegralModel.Finite.Actions.GroupEndRing (A.pullback T.hom))
    (h : IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrict A b r = s) :
    (Over.pullback b.left).map (r.hom _) ≫
        (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.scheme U.hom b.left T.hom b.w).hom =
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso A.scheme U.hom b.left T.hom b.w).hom ≫ s.hom _ := by
  have hh := congrArg (fun q : IntegralModel.Finite.Actions.GroupEndRing (A.pullback T.hom) => q.hom _) h
  change (IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A b).inv ≫ (Over.pullback b.left).map (r.hom _) ≫
    (IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A b).hom = s.hom _ at hh
  have hc := congrArg (fun q => (IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A b).hom ≫ q) hh
  rw [Iso.hom_inv_id_assoc] at hc
  rw [endomorphism_restrictionIso_eq_iterated] at hc
  exact hc

theorem arithmetic_endomorphism_restrict_compatibility
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of K))) (F : IntegralModel.Base.ArithmeticBaseExtension K κ)
    (r : IntegralModel.Finite.Actions.GroupEndRing (A.pullback F.fieldExtension))
    (s : IntegralModel.Finite.Actions.GroupEndRing (A.pullback (Spec.map (CommRingCat.ofHom κ))))
    (h : IntegralModel.EndomorphismFamiliesId.EndomorphismFamilies.restrict A F.complexFieldMap r = s) :
    (Over.pullback (Spec.map (CommRingCat.ofHom F.embedding))).map (r.hom _) ≫
        (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F A.scheme).hom =
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso F A.scheme).hom ≫ s.hom _ :=
  endomorphism_restrict_compatibility A F.complexFieldMap r s h

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EndomorphismParameterDescent
