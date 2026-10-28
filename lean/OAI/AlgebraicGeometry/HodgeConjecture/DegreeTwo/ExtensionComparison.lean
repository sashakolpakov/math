import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BoundedFlasqueSections

/-! # Extension Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExtensionComparison.Constructions

noncomputable section

/-! Restriction and additive functors retain the actual maps of complexes extended by zero. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable (e : c.Embedding c') [e.IsRelIff]

theorem strictSupportRestrictionExtendMap_naturality {K L : HomologicalComplex C c'}
    [K.IsStrictlySupported e] [L.IsStrictlySupported e] (f : K ⟶ L) :
    f ≫ BoundedFlasqueSections.Constructions.strictSupportRestrictionExtendMap L e =
      BoundedFlasqueSections.Constructions.strictSupportRestrictionExtendMap K e ≫ extendMap (restrictionMap f e) e := by
  ext i' : 1
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i,rfl⟩ := hi'
    simp [BoundedFlasqueSections.Constructions.strictSupportRestrictionExtendMap, e.liftExtend_f _ _ rfl,
      extendMap_f _ _ rfl, restrictionXIso]
    change f.f (e.f i) ≫ 𝟙 (L.X (e.f i)) = 𝟙 (K.X (e.f i)) ≫ f.f (e.f i)
    rw [Category.comp_id, Category.id_comp]
  · exact ((L.restriction e).isZero_extend_X e i' (by simpa using hi')).eq_of_tgt _ _

theorem strictSupportRestrictionMap_quasiIso {K L : HomologicalComplex C c'}
    [K.IsStrictlySupported e] [L.IsStrictlySupported e] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (restrictionMap f e) := by
  have := BoundedFlasqueSections.Constructions.strictSupportRestrictionExtendMap_isIso K e
  have := BoundedFlasqueSections.Constructions.strictSupportRestrictionExtendMap_isIso L e
  have h : QuasiIso (f ≫ BoundedFlasqueSections.Constructions.strictSupportRestrictionExtendMap L e) := inferInstance
  rw [strictSupportRestrictionExtendMap_naturality] at h
  have := quasiIso_of_comp_left (BoundedFlasqueSections.Constructions.strictSupportRestrictionExtendMap K e)
    (extendMap (restrictionMap f e) e)
  exact (quasiIso_extendMap_iff (restrictionMap f e) e).mp this

variable (F : C ⥤ D) [F.Additive]

def functorExtendRestrictionIso (K : HomologicalComplex C c) :
    (((F.mapHomologicalComplex c').obj (K.extend e)).restriction e) ≅
      (F.mapHomologicalComplex c).obj K := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => F.mapIso (K.extendXIso e (i := i) rfl)) ?_
  intro i j hij
  symm
  change F.map ((K.extend e).d (e.f i) (e.f j)) ≫ F.map (K.extendXIso e (i := j) rfl).hom =
    F.map (K.extendXIso e (i := i) rfl).hom ≫ F.map (K.d i j)
  rw [← Functor.map_comp, ← Functor.map_comp, K.extend_d_eq e rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem functorExtendRestrictionIso_naturality {K L : HomologicalComplex C c} (f : K ⟶ L) :
    restrictionMap ((F.mapHomologicalComplex c').map (extendMap f e)) e ≫
        (functorExtendRestrictionIso e F L).hom =
      (functorExtendRestrictionIso e F K).hom ≫ (F.mapHomologicalComplex c).map f := by
  ext i : 1
  change F.map ((extendMap f e).f (e.f i)) ≫ F.map (L.extendXIso e (i := i) rfl).hom =
    F.map (K.extendXIso e (i := i) rfl).hom ≫ F.map (f.f i)
  rw [← Functor.map_comp, ← Functor.map_comp, extendMap_f f e rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem functorQuasiIso_of_extended {K L : HomologicalComplex C c} (f : K ⟶ L)
    [QuasiIso ((F.mapHomologicalComplex c').map (extendMap f e))] :
    QuasiIso ((F.mapHomologicalComplex c).map f) := by
  have := strictSupportRestrictionMap_quasiIso e
    ((F.mapHomologicalComplex c').map (extendMap f e))
  have h : QuasiIso (restrictionMap ((F.mapHomologicalComplex c').map (extendMap f e)) e ≫
      (functorExtendRestrictionIso e F L).hom) := inferInstance
  rw [functorExtendRestrictionIso_naturality] at h
  exact quasiIso_of_comp_left (functorExtendRestrictionIso e F K).hom _

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExtensionComparison.Constructions
