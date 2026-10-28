import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField

/-! # Function Fields -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A finitely generated field tower of equal finite transcendence degrees
has finite degree over the intermediate field. -/
theorem finite_of_equal_trdeg (K E L : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [FinTrdeg K E] [Algebra.EssFiniteType K L]
    (h : Algebra.trdeg K E = Algebra.trdeg K L) : Module.Finite E L := by
  have hsum : Algebra.trdeg K E + Algebra.trdeg E L = Algebra.trdeg K E :=
    (trdeg_add_eq K E (A := L)).trans h.symm
  have hz : Algebra.trdeg E L = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hsum with hlarge | hzero
    · exact (not_le_of_gt (trdeg_lt_aleph0 K E)
        ((le_max_left _ _).trans hlarge)).elim
    · exact hzero
  let : Algebra.IsAlgebraic E L := trdeg_eq_zero_iff.mp hz
  let : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp K E L
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

variable {S T : Scheme.{u}} [IsIntegral S] [IsIntegral T]

/-- The actual generic-stalk pullback of a dominant morphism. -/
def genericFieldMap (i : S ⟶ T) (hη : i (genericPoint S) = genericPoint T) :
    T.functionField ⟶ S.functionField :=
  (T.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫
    i.stalkMap (genericPoint S)

theorem genericFieldMap_germ (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) :
    T.presheaf.germ ⊤ (genericPoint T) (by trivial) ≫ genericFieldMap i hη =
      i.appTop ≫ S.presheaf.germ ⊤ (genericPoint S) (by trivial) := by
  simp only [genericFieldMap, TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  have h := T.presheaf.germ_stalkSpecializes
    (show genericPoint T ∈ (⊤ : T.Opens) from trivial)
    (Inseparable.of_eq hη).specializes
  exact (congrArg
    (fun k : Γ(T, ⊤) ⟶ T.presheaf.stalk (i (genericPoint S)) =>
      k ≫ i.stalkMap (genericPoint S)) h).trans
    (i.germ_stalkMap ⊤ (genericPoint S) (by trivial))

theorem genericFieldMap_base {B : Scheme.{u}} (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ B) :
    Betti.AffineDimension.Realization.functionFieldBaseMap g ≫ genericFieldMap i hη =
      Betti.AffineDimension.Realization.functionFieldBaseMap (i ≫ g) := by
  simp only [Betti.AffineDimension.Realization.functionFieldBaseMap, Scheme.Hom.comp_appTop, Category.assoc]
  rw [genericFieldMap_germ]

variable {K : Type u} [Field K]

theorem genericFieldMap_scalar (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of K)) :
    (genericFieldMap i hη).hom.comp (Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap g) =
      Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap (i ≫ g) := by
  exact congrArg
    (fun h : Γ(Spec (.of K), ⊤) ⟶ S.functionField =>
      h.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    (genericFieldMap_base i hη g)

/-- The function-field embedding respects the specified ground field. -/
def genericFieldAlgHom (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of K)) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
    T.functionField →ₐ[K] S.functionField := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
  exact { (genericFieldMap i hη).hom with
    commutes' := fun c => DFunLike.congr_fun (genericFieldMap_scalar i hη g) c }

/-- A dominant map cannot increase the dimension of its image. -/
theorem dimension_le_of_genericPoint (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of K))
    [LocallyOfFiniteType g] [LocallyOfFiniteType (i ≫ g)] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
  apply (Nat.cast_le (α := Cardinal)).mp
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast, Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast]
  exact trdeg_le_of_injective (genericFieldAlgHom i hη g)
    (genericFieldAlgHom i hη g).injective

/-- In the dimension-preserving case the actual generic-field embedding
is finite; this is not a finiteness assumption on the morphism. -/
theorem genericField_extension_finite (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) (g : T ⟶ Spec (.of K))
    [LocallyOfFiniteType g] [LocallyOfFiniteType (i ≫ g)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ g)) :
    letI := (genericFieldMap i hη).hom.toAlgebra
    Module.Finite T.functionField S.functionField := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ g)
  let := (genericFieldMap i hη).hom.toAlgebra
  let : IsScalarTower K T.functionField S.functionField :=
    IsScalarTower.of_algHom (genericFieldAlgHom i hη g)
  let := Foundations.Scheme.FunctionFieldFiniteType.functionFieldScalar_finTrdeg g
  let := Foundations.Scheme.FunctionFieldFiniteType.functionFieldScalar_essFiniteType (i ≫ g)
  apply finite_of_equal_trdeg K T.functionField S.functionField
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast, ← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast, hdim]

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields.Construction
