import OAI.AlgebraicGeometry.Divisors.LineBundles.ValuativeCenterPoint
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-! # Valuation Extension Of -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ValuationExtensionOf.BundleCycles.ValuationExtension

noncomputable section

/-! A generic map into a proper separated scheme extends across every
valuation-ring stalk. The local lifts spread out and form a rational map
whose domain is the whole source. -/

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
  let qhom : ((⊤ : X.Opens) : Scheme) ⟶ Y := q.hom
  let i := X.topIso.inv ≫ qhom
  have hi : i.toPartialMap = q := by
    apply PartialMap.ext i.toPartialMap q rfl
    change X.topIso.hom ≫ X.topIso.inv ≫ qhom =
      (X.isoOfEq (rfl : (⊤ : X.Opens) = ⊤)).hom ≫ qhom
    rw [Iso.hom_inv_id_assoc, Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  refine ⟨i, ?_⟩
  change i.toPartialMap.toRationalMap = r
  rw [hi, PartialMap.restrict_toRationalMap, RationalMap.toRationalMap_toPartialMap]

theorem exists_extension [Y.IsSeparated] [S.IsSeparated]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (φ : Spec X.functionField ⟶ Y) (hφ : φ ≫ sY = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ≫ sX)
    (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    ∃ i : X ⟶ Y, IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ≫ i = φ ∧ i ≫ sY = sX := by
  have hp : ValuativeCriterion sY := by
    have h : IsProper sY := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  let r := RationalMap.ofFunctionField sX sY φ hφ
  have hR : r.fromFunctionField = φ :=
    RationalMap.fromFunctionField_ofFunctionField sX sY φ hφ
  have hr : r.domain = ⊤ := by
    apply top_unique
    intro x _
    let := hval x
    let sq : ValuativeCommSq sY :=
      { R := X.presheaf.stalk x
        commRing := (X.presheaf.stalk x).commRing
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
    have hpj : p.fromSpecStalkOfMem hx = j :=
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY j hj₂
    exact (partialMap_generic_from_stalk p x hx).symm.trans
      ((congrArg (fun t : Spec (X.presheaf.stalk x) ⟶ Y =>
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ t) hpj).trans
          (hj₁.trans hR.symm))
  obtain ⟨i, hi⟩ := rationalMap_exists_hom_of_domain_top r hr
  have hgeneric : IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X ≫ i = φ := by
    have h := congrArg RationalMap.fromFunctionField hi
    change i.toPartialMap.fromFunctionField = r.fromFunctionField at h
    have he := h.trans hR
    simpa only [IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap, PartialMap.fromFunctionField,
      PartialMap.fromSpecStalkOfMem_toPartialMap] using he
  refine ⟨i, hgeneric, ?_⟩
  exact ext_of_isDominant (ι := IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X)
    (by rw [← Category.assoc, hgeneric, hφ])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ValuationExtensionOf.BundleCycles.ValuationExtension
