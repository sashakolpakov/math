import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField
import OAI.AlgebraicGeometry.Albanese.Construction.GeneratedClosed

/-! # Dominant Dimension -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.DominantDimension

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- A dominant morphism carries the generic point to the generic point. -/
theorem dominant_genericPoint (i : X ⟶ Y) [IsDominant i] :
    i (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  simpa only [Set.image_univ, i.denseRange.closure_eq] using
    (genericPoint_spec X).image i.continuous

/-- The homomorphism of actual function fields induced by a dominant morphism. -/
def dominantFunctionFieldMap (i : X ⟶ Y) [IsDominant i] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq (dominant_genericPoint i).symm)).hom ≫
    i.stalkMap (genericPoint X)

set_option backward.isDefEq.respectTransparency.types false in
theorem dominantFunctionFieldMap_germ (i : X ⟶ Y) [IsDominant i] :
    Y.presheaf.germ ⊤ (genericPoint Y) (by trivial) ≫ dominantFunctionFieldMap i =
      i.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) (by trivial) := by
  simp only [dominantFunctionFieldMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  rw [TopCat.Presheaf.germ_stalkSpecializes]
  exact i.germ_stalkMap ⊤ (genericPoint X) (by trivial)

theorem dominantFunctionFieldMap_base {S : Scheme.{u}}
    (i : X ⟶ Y) [IsDominant i] (f : Y ⟶ S) :
    Betti.AffineDimension.Realization.functionFieldBaseMap f ≫ dominantFunctionFieldMap i =
      Betti.AffineDimension.Realization.functionFieldBaseMap (i ≫ f) := by
  simp only [Betti.AffineDimension.Realization.functionFieldBaseMap, Scheme.Hom.comp_appTop, Category.assoc]
  rw [dominantFunctionFieldMap_germ]

variable {K : Type u} [Field K]

theorem dominantFunctionFieldMap_scalar (i : X ⟶ Y) [IsDominant i]
    (f : Y ⟶ Spec (.of K)) :
    (dominantFunctionFieldMap i).hom.comp (Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap f) =
      Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap (i ≫ f) :=
  congrArg (fun g : Γ(Spec (.of K), ⊤) ⟶ X.functionField =>
    g.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) (dominantFunctionFieldMap_base i f)

/-- Dominant pullback respects the canonical scalar field structures. -/
def dominantFunctionFieldAlgHom (i : X ⟶ Y) [IsDominant i]
    (f : Y ⟶ Spec (.of K)) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
    Y.functionField →ₐ[K] X.functionField := by
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  exact { (dominantFunctionFieldMap i).hom with
    commutes' := fun c => DFunLike.congr_fun (dominantFunctionFieldMap_scalar i f) c }

/-- A dominant morphism between integral finite-type schemes cannot increase
dimension from its source to its target. -/
theorem dominant_dimension_le [IsIntegral X] [IsIntegral Y]
    (i : X ⟶ Y) [IsDominant i] (f : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [LocallyOfFiniteType (i ≫ f)] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) := by
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let _ := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  apply (Nat.cast_le (α := Cardinal)).mp
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast f, Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast (i ≫ f)]
  exact trdeg_le_of_injective (dominantFunctionFieldAlgHom i f)
    (dominantFunctionFieldAlgHom i f).injective

/-- Dimensions decrease along homomorphic refinements of generated targets. -/
theorem refinement_dimension_le (V : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : V.toOver ⟶ A.toOver) (b : V.toOver ⟶ B.toOver)
    (φ : A.toOver ⟶ B.toOver) [IsMonHom φ] (hφ : a ≫ φ = b)
    (hb : GeneratedClosed.Generates V B b) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap := by
  have : IsIntegral A.toOver.left := inferInstanceAs (IsIntegral A.carrier)
  have : IsIntegral B.toOver.left := inferInstanceAs (IsIntegral B.carrier)
  have : Surjective φ.left := GeneratedClosed.refinement_surjective V A B a b φ hφ hb
  have : IsDominant φ.left := ⟨φ.left.surjective.denseRange⟩
  have : LocallyOfFiniteType A.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType A.variety.structureMap)
  have : LocallyOfFiniteType B.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType B.variety.structureMap)
  have : LocallyOfFiniteType (φ.left ≫ B.toOver.hom) := by rw [φ.w]; infer_instance
  have hd := dominant_dimension_le φ.left B.toOver.hom
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.toOver.hom ≤
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.toOver.hom
  simpa only [φ.w] using hd

end

end OAI.AlgebraicGeometry.Albanese.Construction.DominantDimension
