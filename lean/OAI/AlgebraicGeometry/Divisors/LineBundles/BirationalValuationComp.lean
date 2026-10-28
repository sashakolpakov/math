import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationOf
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

/-! # Birational Valuation Comp -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationComp.BundleCycles.BirationalValuationSection

noncomputable section

/-! Above a valuation-ring point, the actual inverse stalk isomorphism
constructs a local section of a birational scheme map. Separatedness will
compare these sections through their common generic restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
  [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (y : Y) (x : X) (hx : f x = y)

def pointStalkMap : Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  (Y.presheaf.stalkCongr (Inseparable.of_eq hx.symm)).hom ≫ f.stalkMap x

omit [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] [IsIntegral X] [IsIntegral Y] in
theorem pointStalkMap_self : pointStalkMap f (f x) x rfl = f.stalkMap x := by
  unfold pointStalkMap
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

include hη in
theorem pointStalkMap_isIso [ValuationRing (Y.presheaf.stalk y)] :
    IsIso (pointStalkMap f y x hx) := by
  let : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  let := BirationalValuationOf.BundleCycles.BirationalValuationStalk.stalkMap_isIso_of_valuation f hη x
  unfold pointStalkMap
  infer_instance

omit [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] in
theorem pointStalkMap_functionField :
    pointStalkMap f y x hx ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Y.functionField) ≫
        Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη := by
  subst y
  rw [pointStalkMap_self]
  ext a
  exact (RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x a).symm

def localSection [ValuationRing (Y.presheaf.stalk y)] : Spec (Y.presheaf.stalk y) ⟶ X :=
  letI := pointStalkMap_isIso f hη y x hx
  Spec.map (asIso (pointStalkMap f y x hx)).inv ≫ X.fromSpecStalk x

theorem localSection_comp [ValuationRing (Y.presheaf.stalk y)] :
    localSection f hη y x hx ≫ f = Y.fromSpecStalk y := by
  subst y
  let := pointStalkMap_isIso f hη (f x) x rfl
  have he : f.stalkMap x ≫ (asIso (pointStalkMap f (f x) x rfl)).inv = 𝟙 _ := by
    exact (congrArg (fun t => t ≫ (asIso (pointStalkMap f (f x) x rfl)).inv)
      (pointStalkMap_self f x).symm).trans (asIso (pointStalkMap f (f x) x rfl)).hom_inv_id
  change (Spec.map (asIso (pointStalkMap f (f x) x rfl)).inv ≫ X.fromSpecStalk x) ≫ f = _
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, he]
  simp

theorem localSection_closedPoint [ValuationRing (Y.presheaf.stalk y)] :
    localSection f hη y x hx (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = x := by
  let := pointStalkMap_isIso f hη y x hx
  change X.fromSpecStalk x ((Spec.map (asIso (pointStalkMap f y x hx)).inv)
    (IsLocalRing.closedPoint (Y.presheaf.stalk y))) = x
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := (asIso (pointStalkMap f y x hx)).inv))).trans
    (Scheme.fromSpecStalk_closedPoint (X := X) (x := x))

def genericApproachMap : Spec X.functionField ⟶ Spec (Y.presheaf.stalk y) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Y.functionField) ≫
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)

omit [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] in
instance genericApproachMap_isDominant : IsDominant (genericApproachMap f hη y) := by
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap
    ((Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.comp (algebraMap (Y.presheaf.stalk y) Y.functionField)))
  have hi : Function.Injective ((Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.comp
      (algebraMap (Y.presheaf.stalk y) Y.functionField)) :=
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.injective.comp
      (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp hi]
  exact bot_le

theorem genericApproach_localSection [ValuationRing (Y.presheaf.stalk y)] :
    genericApproachMap f hη y ≫ localSection f hη y x hx = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X := by
  let := pointStalkMap_isIso f hη y x hx
  let e := asIso (pointStalkMap f y x hx)
  let a := CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)
  let b := CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Y.functionField) ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη
  have hf : e.hom ≫ a = b := pointStalkMap_functionField f hη y x hx
  have he : e.inv ≫ b = a :=
    (congrArg (fun t => e.inv ≫ t) hf.symm).trans (Iso.inv_hom_id_assoc e a)
  change Spec.map b ≫ (Spec.map e.inv ≫ X.fromSpecStalk x) = _
  rw [← Spec.map_comp_assoc]
  have hs : Spec.map a ≫ X.fromSpecStalk x = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X := by
    change Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫
      X.fromSpecStalk x = _
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X).specializes trivial)
  exact (congrArg (fun t => Spec.map t ≫ X.fromSpecStalk x) he).trans hs

include hη in
theorem valuationFiber_unique [IsSeparated f] [ValuationRing (Y.presheaf.stalk y)]
    (x₁ x₂ : X) (h₁ : f x₁ = y) (h₂ : f x₂ = y) : x₁ = x₂ := by
  have hs : localSection f hη y x₁ h₁ = localSection f hη y x₂ h₂ :=
    ext_of_isDominant_of_isSeparated f
      ((localSection_comp f hη y x₁ h₁).trans (localSection_comp f hη y x₂ h₂).symm)
      (genericApproachMap f hη y)
      ((genericApproach_localSection f hη y x₁ h₁).trans
        (genericApproach_localSection f hη y x₂ h₂).symm)
  have h := congrArg (fun s : Spec (Y.presheaf.stalk y) ⟶ X =>
    s (IsLocalRing.closedPoint (Y.presheaf.stalk y))) hs
  simpa only [localSection_closedPoint] using h

include hη in
theorem proper_valuationFiber_unique [IsProper f] [ValuationRing (Y.presheaf.stalk y)] :
    ∃! x : X, f x = y := by
  let : IsDominant f := by
    refine ⟨?_⟩
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_spec Y]
    apply closure_mono
    exact Set.singleton_subset_iff.mpr ⟨genericPoint X, hη⟩
  let : Surjective f := surjective_of_isDominant_of_isClosed_range f
    (f.isClosedMap.isClosed_range)
  obtain ⟨a, ha⟩ := f.surjective y
  exact ⟨a, ha, fun b hb => valuationFiber_unique f hη y b a hb ha⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationComp.BundleCycles.BirationalValuationSection
