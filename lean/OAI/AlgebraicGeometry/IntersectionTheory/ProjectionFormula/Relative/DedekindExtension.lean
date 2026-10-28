import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DedekindExtension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberFields

/-! # Dedekind Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.DedekindExtension

noncomputable section

/-! A Dedekind model of the source function field extends into a proper
morphism over the generic point of its integral base. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField

universe u

theorem exists_extension {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y) [IsProper f]
    (hη : f (genericPoint X) = genericPoint Y)
    (A : Type u) [CommRing A] [IsDedekindDomain A]
    [Algebra Y.functionField A] [Algebra A X.functionField] [IsFractionRing A X.functionField]
    (hscalar : (algebraMap A X.functionField).comp (algebraMap Y.functionField A) =
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom) :
    ∃ i : Spec (.of A) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫ i = Normalization.Scheme.genericMap X ∧
        i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Y.functionField A)) ≫ Normalization.Scheme.genericMap Y := by
  let e := Affine.FractionField.fieldIso A X.functionField
  let φ := Spec.map e.inv ≫ Normalization.Scheme.genericMap X
  let sA := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField A)) ≫ Normalization.Scheme.genericMap Y
  have hc : φ ≫ f = Normalization.Scheme.genericMap (Spec (.of A)) ≫ sA := by
    dsimp only [φ, sA]
    rw [Category.assoc, ← Normalization.Functor.genericMap_square f hη,
      ← Category.assoc, ← Spec.map_comp]
    dsimp only [Normalization.Scheme.genericMap]
    rw [Spec.fromSpecStalk_eq', ← Category.assoc, ← Spec.map_comp]
    congr 2
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, Affine.FractionField.toStalk_fieldIso]
    exact congrArg CommRingCat.ofHom hscalar.symm
  obtain ⟨i, hi, hf⟩ := ValuationExtension.exists_extension sA f φ hc
    (DedekindExtension.stalk_valuation A)
  refine ⟨i, ?_, hf⟩
  have hgeneric : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) =
      Spec.map e.hom ≫ Normalization.Scheme.genericMap (Spec (.of A)) := by
    rw [Normalization.Scheme.genericMap, Spec.fromSpecStalk_eq', ← Spec.map_comp, Affine.FractionField.toStalk_fieldIso]
  rw [hgeneric, Category.assoc, hi]
  simp [φ, ← Spec.map_comp_assoc]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.DedekindExtension
