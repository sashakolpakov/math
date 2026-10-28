import OAI.AlgebraicGeometry.Divisors.LineBundles.DedekindStalkValuation
import OAI.AlgebraicGeometry.Divisors.LineBundles.ValuationExtensionOf
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberEss

/-! # Dedekind Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.DedekindExtension.BundleCycles.RelativeDedekindExtension

noncomputable section

/-! A Dedekind model of the source function field extends into a proper
morphism over the generic point of its integral base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.FractionField.BundleCycles.AffineFractionField

universe u

theorem exists_extension {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y) [IsProper f]
    (hη : f (genericPoint X) = genericPoint Y)
    (A : Type u) [CommRing A] [IsDedekindDomain A]
    [Algebra Y.functionField A] [Algebra A X.functionField] [IsFractionRing A X.functionField]
    (hscalar : (algebraMap A X.functionField).comp (algebraMap Y.functionField A) =
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom) :
    ∃ i : Spec (.of A) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫ i = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ∧
        i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Y.functionField A)) ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y := by
  let e := Affine.FractionField.BundleCycles.AffineFractionField.fieldIso A X.functionField
  let φ := Spec.map e.inv ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X
  let sA := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField A)) ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y
  let t : CommRingCat.of A ⟶ (Spec (.of A)).functionField :=
    StructureSheaf.toStalk A (genericPoint (Spec (.of A)))
  let b : Y.functionField ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap Y.functionField A)
  have ht : t ≫ e.hom = CommRingCat.ofHom (algebraMap A X.functionField) := Affine.FractionField.BundleCycles.AffineFractionField.toStalk_fieldIso A X.functionField
  have hgen : IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap (Spec (.of A)) = Spec.map t := Spec.fromSpecStalk_eq' _ _
  have hfield : Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη ≫ e.inv = b ≫ t := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, ht]
    exact congrArg CommRingCat.ofHom hscalar.symm
  have hc : φ ≫ f = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap (Spec (.of A)) ≫ sA := by
    change (Spec.map e.inv ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X) ≫ f = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap (Spec (.of A)) ≫ (Spec.map b ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y)
    rw [Category.assoc, ← NormalizationFunctorTo.BundleCycles.NormalizationFunctor.genericMap_square f hη,
      ← Category.assoc, ← Spec.map_comp, hfield, Spec.map_comp, Category.assoc, ← hgen]
  obtain ⟨i, hi, hf⟩ := ValuationExtensionOf.BundleCycles.ValuationExtension.exists_extension sA f φ hc
    (DedekindStalkValuation.BundleCycles.stalk_valuation A)
  refine ⟨i, ?_, hf⟩
  have hgeneric : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) =
      Spec.map e.hom ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap (Spec (.of A)) :=
    (congrArg Spec.map ht).symm.trans ((Spec.map_comp t e.hom).trans
      (congrArg (fun j : Spec (Spec (.of A)).functionField ⟶ Spec (.of A) => Spec.map e.hom ≫ j) hgen.symm))
  rw [hgeneric, Category.assoc, hi]
  simp [φ, ← Spec.map_comp_assoc]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.DedekindExtension.BundleCycles.RelativeDedekindExtension
