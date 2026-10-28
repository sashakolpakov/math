import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuationExtension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveLocalRings
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BranchStalkField
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenterFields

/-! # Dedekind Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DedekindExtension

noncomputable section

/-! The normalized parameter ring maps to a proper curve by extending
its prescribed function-field map. This construction includes all of its
branches at once and fixes the generic-field coordinates. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.FractionField

universe u

theorem stalk_valuation (A : Type u) [CommRing A] [IsDedekindDomain A]
    (x : Spec (.of A)) : ValuationRing ((Spec (.of A)).presheaf.stalk x) := by
  let : Algebra A ((Spec (.of A)).presheaf.stalk x) := StructureSheaf.stalkAlgebra A x
  let : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A x
  let : IsDedekindDomain ((Spec (.of A)).presheaf.stalk x) :=
    IsLocalization.AtPrime.isDedekindDomain A x.asIdeal _
  exact CurveLocalRings.normal_local_valuation _

theorem exists_extension {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (A : Type u) [CommRing A] [IsDedekindDomain A]
    [Algebra k A] [Algebra A X.functionField] [IsFractionRing A X.functionField]
    (hscalar : (algebraMap A X.functionField).comp (algebraMap k A) = Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap f) :
    ∃ i : Spec (.of A) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫ i = Normalization.Scheme.genericMap X ∧
        i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  let e := Affine.FractionField.fieldIso A X.functionField
  let φ := Spec.map e.inv ≫ Normalization.Scheme.genericMap X
  let sA := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have hc : φ ≫ f = Normalization.Scheme.genericMap (Spec (.of A)) ≫ sA := by
    dsimp only [φ, sA]
    rw [Category.assoc, ← ValuativeCenter.genericMap_scalar,
      Normalization.Scheme.genericMap, Spec.fromSpecStalk_eq', ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      Affine.FractionField.toStalk_fieldIso]
    exact congrArg CommRingCat.ofHom hscalar.symm
  obtain ⟨i, hi, hf⟩ := ValuationExtension.exists_extension sA f φ hc (stalk_valuation A)
  refine ⟨i, ?_, hf⟩
  have hgeneric : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) =
      Spec.map e.hom ≫ Normalization.Scheme.genericMap (Spec (.of A)) := by
    rw [Normalization.Scheme.genericMap, Spec.fromSpecStalk_eq', ← Spec.map_comp, Affine.FractionField.toStalk_fieldIso]
  rw [hgeneric, Category.assoc, hi]
  simp [φ, ← Spec.map_comp_assoc]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DedekindExtension
