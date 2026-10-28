import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuativeCenter
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-! # Valuation Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuationExtension

noncomputable section

/-! A generic map into a proper separated scheme extends across every
valuation-ring stalk. The local lifts spread out and form a rational map
whose domain is the whole source. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

universe u

variable {X Y S : Scheme.{u}} [IsIntegral X]

theorem partialMap_generic_from_stalk (p : X.PartialMap Y) (x : X) (hx : x ∈ p.domain) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      p.fromSpecStalkOfMem hx = p.fromFunctionField := by
  unfold PartialMap.fromFunctionField PartialMap.fromSpecStalkOfMem
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono p.domain.ι).mp
  rw [Category.assoc, Opens.fromSpecStalkOfMem_ι, Opens.fromSpecStalkOfMem_ι]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    ((genericPoint_spec X).specializes trivial)

theorem rationalMap_exists_hom_of_domain_top [Y.IsSeparated] (r : X.RationalMap Y)
    (hr : r.domain = ⊤) : ∃ i : X ⟶ Y, i.toRationalMap = r := by
  let p := r.toPartialMap
  have hp : p.domain = ⊤ := hr
  let q := p.restrict ⊤ dense_univ (le_of_eq hp.symm)
  let i := X.topIso.inv ≫ q.hom
  have hi : i.toPartialMap = q := by
    apply PartialMap.ext i.toPartialMap q rfl
    simp [Hom.toPartialMap, i]
  refine ⟨i, ?_⟩
  change i.toPartialMap.toRationalMap = r
  rw [hi, PartialMap.restrict_toRationalMap, RationalMap.toRationalMap_toPartialMap]

theorem exists_extension [Y.IsSeparated] [S.IsSeparated]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (φ : Spec X.functionField ⟶ Y) (hφ : φ ≫ sY = Normalization.Scheme.genericMap X ≫ sX)
    (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    ∃ i : X ⟶ Y, Normalization.Scheme.genericMap X ≫ i = φ ∧ i ≫ sY = sX := by
  have hp : ValuativeCriterion sY := by
    have h : IsProper sY := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  let r := RationalMap.ofFunctionField sX sY φ hφ
  have hr : r.domain = ⊤ := by
    apply top_unique
    intro x _
    let := hval x
    let sq : ValuativeCommSq sY :=
      { R := X.presheaf.stalk x
        K := X.functionField
        i₁ := φ
        i₂ := X.fromSpecStalk x ≫ sX
        commSq := ⟨by
          rw [hφ, ← Category.assoc]
          congr 1
          exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
            ((genericPoint_spec X).specializes trivial)).symm⟩ }
    obtain ⟨j, hj₁, hj₂⟩ := (hp.existence sq).exists_lift
    let p := PartialMap.ofFromSpecStalk sX sY j hj₂
    have hx : x ∈ p.domain := PartialMap.mem_domain_ofFromSpecStalk sX sY j hj₂
    apply RationalMap.mem_domain.mpr
    refine ⟨p, hx, RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
    change p.fromFunctionField = r.fromFunctionField
    rw [RationalMap.fromFunctionField_ofFunctionField]
    rw [← partialMap_generic_from_stalk p x hx,
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hj₁
  obtain ⟨i, hi⟩ := rationalMap_exists_hom_of_domain_top r hr
  have hgeneric : Normalization.Scheme.genericMap X ≫ i = φ := by
    have h := congrArg RationalMap.fromFunctionField hi
    change i.toPartialMap.fromFunctionField = r.fromFunctionField at h
    rw [RationalMap.fromFunctionField_ofFunctionField] at h
    simpa only [Normalization.Scheme.genericMap, PartialMap.fromFunctionField,
      PartialMap.fromSpecStalkOfMem_toPartialMap] using h
  refine ⟨i, hgeneric, ?_⟩
  exact ext_of_isDominant (ι := Normalization.Scheme.genericMap X)
    (by rw [← Category.assoc, hgeneric, hφ])

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuationExtension
