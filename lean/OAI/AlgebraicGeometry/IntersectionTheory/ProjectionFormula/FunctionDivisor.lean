import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison

/-! # Function Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FunctionDivisor

noncomputable section

/-! Nonzero rational functions algebraic over the ground field have zero
principal divisor. Normal local rings contain both the function and its
inverse; finite normalization extends the conclusion to singular schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

theorem algebraic_isUnit_integer (k R L : Type*) [Field k] [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field L] [Algebra k R] [Algebra k L] [Algebra R L]
    [IsScalarTower k R L] [IsFractionRing R L] (g : L) (hg : g ≠ 0) (ha : IsAlgebraic k g) :
    ∃ a : R, IsUnit a ∧ algebraMap R L a = g := by
  obtain ⟨a, ha'⟩ := (isIntegrallyClosed_iff L).mp ‹IsIntegrallyClosed R› ha.isIntegral.tower_top
  obtain ⟨b, hb'⟩ := (isIntegrallyClosed_iff L).mp ‹IsIntegrallyClosed R› ha.inv.isIntegral.tower_top
  refine ⟨a, IsUnit.of_mul_eq_one b ?_, ha'⟩
  apply IsFractionRing.injective R L
  rw [map_mul, ha', hb', mul_inv_cancel₀ hg, map_one]

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

abbrev stalkScalarAlgebra (f : X ⟶ Spec (.of k)) (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x (by trivial)).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)).toAlgebra

theorem stalkScalarTower (f : X ⟶ Spec (.of k)) (x : X) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    letI := stalkScalarAlgebra f x
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let := stalkScalarAlgebra f x
  let : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  apply IsScalarTower.of_algebraMap_eq
  intro c
  exact (Scheme.algebraMap_germ_eq_germToFunctionField X (U := ⊤) (x := x) (by trivial)
    (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c))).symm

theorem ord_eq_zero_of_algebraic [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) (x : X) [IsIntegrallyClosed (X.presheaf.stalk x)]
    (g : X.functionField) (hg : g ≠ 0) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    IsAlgebraic k g → X.ord g x = 0 := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  intro ha
  by_cases hx : coheight x = 1
  · let := stalkScalarAlgebra f x
    let := stalkScalarTower f x
    let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    obtain ⟨a, hau, ha'⟩ := algebraic_isUnit_integer k (X.presheaf.stalk x) X.functionField g hg ha
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
    change WithZero.log (Ring.ordFrac (X.presheaf.stalk x) g) = 0
    rw [← ha', Ring.ordFrac_of_isUnit hau, WithZero.log_one]
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx g

theorem principalDivisor_eq_zero_of_normal [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Spec (.of k))
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : X.functionField) (hg : g ≠ 0) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    IsAlgebraic k g → Affine.DivisorNorm.rationalPrincipalDivisor X g = 0 := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  intro ha
  ext x
  let := hNormal x
  change (X.ord g x : ℚ) = 0
  rw [ord_eq_zero_of_algebraic f x g hg ha, Int.cast_zero]

theorem principalDivisor_eq_zero [AlgebraicGeometry.IsNoetherian X] [CharZero k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (g : X.functionField) (hg : g ≠ 0) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    IsAlgebraic k g → Affine.DivisorNorm.rationalPrincipalDivisor X g = 0 := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  intro ha
  let := Normalization.DivisorComparison.normalization_noetherian X f
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Normalization.Scheme.normalizationMap X ≫ f)
  let hmap := Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom (Normalization.Scheme.normalizationMap X)
    (Normalization.Fields.normalizationMap_genericPoint X) f
  have ha' : IsAlgebraic k ((Normalization.Fields.normalizationFieldIso X).hom g) :=
    (ha.isIntegral.map hmap).isAlgebraic
  have hg' : (Normalization.Fields.normalizationFieldIso X).hom g ≠ 0 :=
    (map_ne_zero_iff _ (Normalization.Fields.normalizationFieldMap_bijective X).injective).mpr hg
  have hz := principalDivisor_eq_zero_of_normal (Normalization.Scheme.normalizationMap X ≫ f)
    (Normalization.Scheme.normalization_stalk_integrallyClosed X)
    ((Normalization.Fields.normalizationFieldIso X).hom g) hg' ha'
  rw [← Normalization.DivisorComparison.normalization_principalDivisor X f g hg, hz, map_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FunctionDivisor
