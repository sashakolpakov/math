import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.TranslationQuotientLine
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceEq
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift

/-! # Translation Picard Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample

noncomputable section

/-! The line descended along the full translation kernel separates
points on every test scheme. The proof uses actual fppf lifts, so it
also retains infinitesimal points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceEq.Geometric

variable {S : Scheme} [IsLocallyNoetherian S] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} {L : Line.Bundles.LineBundle A.scheme.left}
    {P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme} (Q : TranslationQuotient.AmpleTranslationQuotient A L P)

local instance TranslationQuotient.AmpleTranslationQuotient.picardInjection_source_locallyNoetherian : IsLocallyNoetherian A.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom

local instance TranslationQuotient.AmpleTranslationQuotient.picardInjection_isogeny_etale : Etale Q.isogeny.hom.left := Q.etale

theorem TranslationQuotient.AmpleTranslationQuotient.difference_zero_iff_quotient_zero {U : Over S} (a : U ⟶ A.scheme) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a = Picard.PicardSheaf.trivialPicardClass A.scheme U ↔
      a ≫ Q.isogeny.hom = 1 := by
  let : Mono (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P) :=
    Picard.ThetaConstruction.RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroInclusion_mono P (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L)
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization A L P U a).mp h
    apply (Q.kernel U a).mpr
    refine ⟨z, hz, ?_⟩
    intro w hw
    exact (cancel_mono (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZeroInclusion A L P)).mp (hw.trans hz.symm)
  · intro h
    obtain ⟨z, hz, _⟩ := (Q.kernel U a).mp h
    exact (Picard.ThetaConstruction.RelativeDifferenceZeroScheme.Geometric.relativeDifferenceZero_factorization A L P U a).mpr ⟨z, hz⟩

theorem TranslationQuotient.AmpleTranslationQuotient.difference_eq_iff_quotient_eq {U : Over S} (a b : U ⟶ A.scheme) :
    (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a =
        (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue b ↔
      a ≫ Q.isogeny.hom = b ≫ Q.isogeny.hom := by
  rw [Picard.ThetaConstruction.RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_eq_iff_div_zero, Q.difference_zero_iff_quotient_zero,
    MonObj.mul_comp, GrpObj.inv_comp, mul_inv_eq_one]

theorem TranslationQuotient.AmpleTranslationQuotient.descendedDifference_value_pullback {U : Over S} (a : U ⟶ A.scheme) :
    Q.descendedDifference.relativeValue (a ≫ Q.isogeny.hom) =
      (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a := by
  have he : (a ⊗ₘ 𝟙 A.scheme) ≫ (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme) =
      (a ≫ Q.isogeny.hom) ⊗ₘ 𝟙 A.scheme := by simp
  apply congrArg ((Picard.PicardSheaf.toRelativePicard A.scheme).app (op U))
  change Line.Bundles.LineBundle.pullbackClass ((a ≫ Q.isogeny.hom) ⊗ₘ 𝟙 A.scheme).left
      (Line.Bundles.LineBundle.classOf Q.descendedDifference.bundle) =
    Line.Bundles.LineBundle.pullbackClass (a ⊗ₘ 𝟙 A.scheme).left
      (Line.Bundles.LineBundle.classOf (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L))
  rw [← he, Over.comp_left, Line.Bundles.LineBundle.pullbackClass_comp,
    Q.descendedDifference_pullback_class]

theorem TranslationQuotient.AmpleTranslationQuotient.descendedDifference_value_injective (U : Over S) :
    Function.Injective (Q.descendedDifference.relativeValue (T := U)) := by
  intro x y h
  obtain ⟨V, p, a, b, hpflat, hpsurj, _, ha, hb⟩ :=
    FormalGeometry.Completion.FppfPairLift.Construction.fppf_lift_pair Q.isogeny.hom x y
  let : Flat p.left := hpflat
  let : Surjective p.left := hpsurj
  let : Epi p.left := Flat.epi_of_flat_of_surjective p.left
  have he := congrArg ((Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map p.op) h
  rw [Q.descendedDifference.relativeValue_natural,
    Q.descendedDifference.relativeValue_natural, ha, hb,
    Q.descendedDifference_value_pullback, Q.descendedDifference_value_pullback] at he
  have hab := (Q.difference_eq_iff_quotient_eq a b).mp he
  apply Over.OverMorphism.ext
  apply (cancel_epi p.left).mp
  exact congrArg Over.Hom.left (ha.trans (hab.trans hb.symm))

def TranslationQuotient.AmpleTranslationQuotient.descendedDifference_secondAxis :
    (Scheme.Modules.pullback (lift (1 : A.scheme ⟶ Q.target.scheme)
      (𝟙 A.scheme)).left).obj Q.descendedDifference.bundle.sheaf ≅
        Line.Bundles.structureModule A.scheme.left := by
  have heOver : lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme) ≫
      (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme) =
        lift (1 : A.scheme ⟶ Q.target.scheme) (𝟙 A.scheme) := by
    rw [lift_map, MonObj.one_comp, Category.id_comp]
  have he : (lift (1 : A.scheme ⟶ A.scheme) (𝟙 A.scheme)).left ≫
      (Q.isogeny.hom ⊗ₘ 𝟙 A.scheme).left =
        (lift (1 : A.scheme ⟶ Q.target.scheme) (𝟙 A.scheme)).left :=
    congrArg Over.Hom.left heOver
  have hc : Line.Bundles.LineBundle.classOf (Q.descendedDifference.bundle.pullback
      (lift (1 : A.scheme ⟶ Q.target.scheme) (𝟙 A.scheme)).left) =
      Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.trivial A.scheme.left) := by
    change Line.Bundles.LineBundle.pullbackClass
      (lift (1 : A.scheme ⟶ Q.target.scheme) (𝟙 A.scheme)).left
      (Line.Bundles.LineBundle.classOf Q.descendedDifference.bundle) = _
    rw [← he, Line.Bundles.LineBundle.pullbackClass_comp, Q.descendedDifference_pullback_class]
    exact Quotient.sound (Picard.ThetaConstruction.RelativeDifferenceBundle.Geometric.relativeDifferenceBundle_normalized_right A L)
  exact Classical.choice (Quotient.exact hc)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample
