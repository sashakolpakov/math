import OAI.AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateBlowup

/-! # Subset Coordinate Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCoordinateBlowup.Construction

noncomputable section

/-! Smoothness of actual blowups along selected coordinate subsets, including étale base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R σ : Type u} [CommRing R] [DecidableEq σ]

abbrev subsetCoordinateBlowupAlgebra (C : Finset σ) (i : C) :
    Algebra R (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChart (R := R) C i) :=
  ((Blowup.Charts.Construction.blowupChartConstants (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)).comp MvPolynomial.C).toAlgebra

attribute [local instance] subsetCoordinateBlowupAlgebra

def subsetCoordinateBlowupChartAlgEquiv (C : Finset σ) (i : C) :
    SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChart (R := R) C i ≃ₐ[R] MvPolynomial σ R where
  __ := SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChartEquiv C i
  commutes' r := (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial_constants C i (MvPolynomial.C r)).trans
    (SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution_C C i r)

theorem subsetCoordinateBlowupChart_smooth [Finite σ] (C : Finset σ) (i : C) :
    Algebra.Smooth R (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChart (R := R) C i) := by
  let : Algebra.Smooth R (MvPolynomial σ R) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.of_equiv (subsetCoordinateBlowupChartAlgEquiv C i).symm

theorem subsetCoordinateBlowupChart_scheme_smooth [Finite σ] (C : Finset σ) (i : C) :
    AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom
      ((Blowup.Charts.Construction.blowupChartConstants (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)).comp
        (MvPolynomial.C : R →+* MvPolynomial σ R)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
  exact (RingHom.smooth_algebraMap (R := R) (S := SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChart (R := R) C i)).mpr
    (subsetCoordinateBlowupChart_smooth C i)

omit [DecidableEq σ] in
theorem subsetCoordinate_generators_span (C : Finset σ) :
    Submodule.span (MvPolynomial σ R) (Set.range (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C)
    (fun i : C => (SubsetCoordinateBlowup.Construction.subsetCoordinateElement (R := R) C i).property)).mpr
  change Ideal.span (Set.range (fun i : C => (X i.val : MvPolynomial σ R))) =
    Ideal.span (X '' (C : Set σ))
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.property, hi⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, h⟩

omit [DecidableEq σ] in
theorem subsetCoordinateBlowup_basicOpen_cover (C : Finset σ) :
    (⨆ i : C, Proj.basicOpen (ReesGrading.Construction.reesGrade (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C))
      (Blowup.Charts.Construction.reesGenerator (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i))) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (ReesGrading.Construction.reesGrade (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C))
    (fun i => Blowup.Charts.Construction.reesGenerator (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i))
    (fun i => ⟨1, Blowup.Charts.Construction.reesGenerator_mem (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)⟩)
    (CoordinateBlowup.Construction.reesFamily_adjoin_zero (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) _ (subsetCoordinate_generators_span C))

def subsetCoordinateBlowupAffineCover (C : Finset σ) :
    (ReesGrading.Construction.affineBlowup (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C)).AffineOpenCover where
  I₀ := C
  X i := .of (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupChart (R := R) C i)
  f i := Proj.awayι (ReesGrading.Construction.reesGrade (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C))
    (Blowup.Charts.Construction.reesGenerator (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i))
    (Blowup.Charts.Construction.reesGenerator_mem (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)) (by decide)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((subsetCoordinateBlowup_basicOpen_cover C).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (ReesGrading.Construction.reesGrade (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C)) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((subsetCoordinateBlowup_basicOpen_cover C).ge (Set.mem_univ x))).choose_spec

/-- The entire blowup along a selected coordinate subset remains smooth. -/
theorem subsetCoordinateBlowup_smooth [Finite σ] (C : Finset σ) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) := by
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.Smooth.{u})
    (subsetCoordinateBlowupAffineCover (R := R) C).openCover
  intro i
  change C at i
  change Smooth (Proj.awayι (ReesGrading.Construction.reesGrade (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C))
    (Blowup.Charts.Construction.reesGenerator (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i))
    (Blowup.Charts.Construction.reesGenerator_mem (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)) (by decide) ≫
      (ReesGrading.Construction.affineBlowupToSpec (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)))
  rw [← Category.assoc, Blowup.Charts.Construction.affineBlowup_chart_structureMap, ← Spec.map_comp]
  exact subsetCoordinateBlowupChart_scheme_smooth C i

variable {S : Type u} [CommRing S] [Algebra (MvPolynomial σ R) S]
  [Algebra.Etale (MvPolynomial σ R) S]

/-- Smoothness of the selected coordinate blowup persists under an étale ambient map. -/
theorem subsetCoordinateBlowup_smooth_of_etale [Finite σ] (C : Finset σ) :
    Smooth (ReesGrading.Construction.affineBlowupToSpec ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ R) S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial σ R) S)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) := by
  let : Etale (ReesMap.Construction.affineBlowupMap (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C) (algebraMap (MvPolynomial σ R) S)) :=
    Blowup.FlatBaseChange.Construction.affineBlowupMap_etale (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C)
  let : Smooth (ReesGrading.Construction.affineBlowupToSpec (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) := subsetCoordinateBlowup_smooth C
  rw [← Category.assoc, ← Blowup.BaseOpen.Construction.affineBlowupMap_over, Category.assoc]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SubsetCoordinateBlowup.Construction
