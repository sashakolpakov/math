/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
import OAI.AlgebraicGeometry.ComplexPoint.Open
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Projective Hausdorff -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Hausdorff analytifications of projective complex schemes

The analytification of an affine complex scheme is Hausdorff because global regular functions
separate its complex points. Any two points of finite-dimensional projective space lie in a
common affine basic open: an explicit integral linear form can be chosen not to vanish at either
of two homogeneous coordinate vectors. Pulling this open back along a closed projective
presentation proves that every projective complex scheme has Hausdorff analytification.
-/

open _root_.CategoryTheory _root_.Topology

section

open OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

/-- The analytification of an affine complex scheme is Hausdorff. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.t2Space_of_isAffine (X : Over (Spec ↧ℂ)) [IsAffine X.left] :
    @T2Space (ComplexPoint.Basic.ComplexSchemePoint X) ComplexPoint.Basic.Point.analyticTopology := by
  rw [t2Space_iff_nhds]
  intro z w hzw
  have happ : z.left.appTop ≠ w.left.appTop := fun h ↦
    hzw (Over.OverMorphism.ext (ext_of_isAffine (Y := X.left) h))
  have hex : ∃ s : Γ(X.left, ⊤),
      (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appTop s) ≠
        (Scheme.ΓSpecIso ↧ℂ).hom (w.left.appTop s) := by
    by_contra hn
    push Not at hn
    apply happ
    ext s
    exact (Scheme.ΓSpecIso ↧ℂ).commRingCatIsoToRingEquiv.injective (hn s)
  obtain ⟨s, hs⟩ := hex
  have heval : ComplexPoint.Basic.Point.evaluate ⊤ s z ≠ ComplexPoint.Basic.Point.evaluate ⊤ s w := by
    simpa only [ComplexPoint.Basic.ComplexSchemePoint.evaluate_top_eq_appTop] using hs
  obtain ⟨U, V, hU, hV, hzU, hwV, hUV⟩ := t2_separation heval
  refine ⟨ComplexPoint.Basic.Point.evaluate ⊤ s ⁻¹' U,
    (hU.preimage (ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top s)).mem_nhds hzU,
    ComplexPoint.Basic.Point.evaluate ⊤ s ⁻¹' V,
    (hV.preimage (ComplexPoint.Basic.ComplexSchemePoint.continuous_evaluate_top s)).mem_nhds hwV, ?_⟩
  exact hUV.preimage _

/-- A complex scheme whose every pair of complex points lies in a common affine open has a
Hausdorff analytification. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.t2Space_of_pair_mem_affineOpen (X : Over (Spec ↧ℂ))
    (hpair : ∀ z w : ComplexPoint.Basic.ComplexSchemePoint X,
      ∃ U : X.left.Opens, z ∈ ComplexPoint.Basic.Point.overOpen U ∧ w ∈ ComplexPoint.Basic.Point.overOpen U ∧ IsAffine U.toScheme) :
    @T2Space (ComplexPoint.Basic.ComplexSchemePoint X) ComplexPoint.Basic.Point.analyticTopology := by
  rw [t2Space_iff_nhds]
  intro z w hzw
  obtain ⟨U, hzU, hwU, hUaff⟩ := hpair z w
  let : IsAffine (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U).left := hUaff
  let : T2Space (ComplexPoint.Basic.ComplexSchemePoint (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)) :=
    ComplexPoint.Basic.ComplexSchemePoint.t2Space_of_isAffine (ComplexPoint.Basic.ComplexSchemePoint.openScheme X U)
  let : T2Space {q : ComplexPoint.Basic.ComplexSchemePoint X // q ∈ ComplexPoint.Basic.Point.overOpen U} :=
    (ComplexPoint.Basic.ComplexSchemePoint.openHomeomorph X U).t2Space
  let zU : {q : ComplexPoint.Basic.ComplexSchemePoint X // q ∈ ComplexPoint.Basic.Point.overOpen U} := ⟨z, hzU⟩
  let wU : {q : ComplexPoint.Basic.ComplexSchemePoint X // q ∈ ComplexPoint.Basic.Point.overOpen U} := ⟨w, hwU⟩
  have hzwU : zU ≠ wU := fun h ↦ hzw (congrArg Subtype.val h)
  obtain ⟨A, B, hA, hB, hzA, hwB, hAB⟩ := t2_separation hzwU
  let e : {q : ComplexPoint.Basic.ComplexSchemePoint X // q ∈ ComplexPoint.Basic.Point.overOpen U} →
      ComplexPoint.Basic.ComplexSchemePoint X := Subtype.val
  have he : IsOpenEmbedding e := (ComplexPoint.Basic.Point.isOpen_overOpen (X := X) U).isOpenEmbedding_subtypeVal
  refine ⟨e '' A, (he.isOpenMap A hA).mem_nhds ⟨zU, hzA, rfl⟩,
    e '' B, (he.isOpenMap B hB).mem_nhds ⟨wU, hwB, rfl⟩, ?_⟩
  exact Set.disjoint_image_of_injective he.injective hAB

end

namespace ComplexPoint.ProjectiveHausdorff.ComplexProjectiveSpace

open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- There is an integral linear form which is nonzero on each of two nonzero complex coordinate
vectors. -/
lemma exists_common_nonvanishing_linearForm {n : ℕ}
    (v w : Projective.ComplexProjectiveSpace.CoordinateSpace n) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ r : Projective.ComplexProjectiveSpace.UniversalRing n,
      r ∈ Projective.ComplexProjectiveSpace.UniversalGrading n 1 ∧
      (Scheme.ΓSpecIso ↧ℂ).hom (Projective.ComplexProjectiveSpace.coordinateGlobalSectionsHom v r) ≠ 0 ∧
      (Scheme.ΓSpecIso ↧ℂ).hom (Projective.ComplexProjectiveSpace.coordinateGlobalSectionsHom w r) ≠ 0 := by
  let i := Projective.ComplexProjectiveSpace.coordinateIndex v hv
  have hvi : v i ≠ 0 := Projective.ComplexProjectiveSpace.coordinateIndex_ne_zero v hv
  by_cases hwi : w i ≠ 0
  · refine ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X _ _, ?_, ?_⟩
    · simpa using hvi
    · simpa using hwi
  · let j := Projective.ComplexProjectiveSpace.coordinateIndex w hw
    have hwj : w j ≠ 0 := Projective.ComplexProjectiveSpace.coordinateIndex_ne_zero w hw
    have hwi0 : w i = 0 := not_ne_iff.mp hwi
    by_cases hvij : v i + v j ≠ 0
    · refine ⟨MvPolynomial.X i + MvPolynomial.X j,
        (Projective.ComplexProjectiveSpace.UniversalGrading n 1).add_mem
          (MvPolynomial.isHomogeneous_X _ _)
          (MvPolynomial.isHomogeneous_X _ _), ?_, ?_⟩
      · simpa using hvij
      · simpa [Projective.ComplexProjectiveSpace.coordinateGlobalSectionsHom_X, hwi0] using hwj
    · refine ⟨MvPolynomial.X i - MvPolynomial.X j,
        (Projective.ComplexProjectiveSpace.UniversalGrading n 1).sub_mem
          (MvPolynomial.isHomogeneous_X _ _)
          (MvPolynomial.isHomogeneous_X _ _), ?_, ?_⟩
      · push Not at hvij
        have hvj : v j = -v i := by linear_combination hvij
        simp only [map_sub, Projective.ComplexProjectiveSpace.coordinateGlobalSectionsHom_X]
        simp
        rw [hvj]
        simpa using hvi
      · simpa [Projective.ComplexProjectiveSpace.coordinateGlobalSectionsHom_X, hwi0] using hwj

/-- A homogeneous polynomial is nonzero at a coordinate vector exactly when the corresponding
projective point lies in its basic open. -/
lemma chartIntegralProjAt_preimage_basicOpen {n d : ℕ}
    (v : Projective.ComplexProjectiveSpace.CoordinateSpace n) (i : Fin (n + 1)) (hi : v i ≠ 0)
    (r : Projective.ComplexProjectiveSpace.UniversalRing n) (hd : 0 < d) (hr : r ∈ Projective.ComplexProjectiveSpace.UniversalGrading n d) :
    Projective.ComplexProjectiveSpace.chartIntegralProjAt v i hi ⁻¹ᵁ Proj.basicOpen (Projective.ComplexProjectiveSpace.UniversalGrading n) r =
      if Projective.ComplexProjectiveSpace.coordinateEvaluationHom v r = 0 then ⊥ else ⊤ := by
  unfold Projective.ComplexProjectiveSpace.chartIntegralProjAt
  rw [Scheme.Hom.comp_preimage, show Proj.awayι (Projective.ComplexProjectiveSpace.UniversalGrading n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one ⁻¹ᵁ
        Proj.basicOpen (Projective.ComplexProjectiveSpace.UniversalGrading n) r =
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i) hr) from
    Proj.awayι_preimage_basicOpen
      (𝒜 := Projective.ComplexProjectiveSpace.UniversalGrading n) (f := MvPolynomial.X i) (g := r)
      (m := 1) (m' := d)
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one hr hd]
  rw [SpecMap_preimage_basicOpen, show HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i) hr =
      HomogeneousLocalization.Away.mk (Projective.ComplexProjectiveSpace.UniversalGrading n)
        (MvPolynomial.isHomogeneous_X (ULift ℤ) i) d r (by simpa using hr) by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem]]
  simp only [CommRingCat.hom_ofHom]
  rw [Projective.ComplexProjectiveSpace.awayCoordinateEvaluation_mk v i hi d r hr]
  split_ifs with h
  · rw [h, zero_mul, PrimeSpectrum.basicOpen_zero]
    rfl
  · apply top_unique
    intro x hx
    change Projective.ComplexProjectiveSpace.coordinateEvaluationHom v r * (v i)⁻¹ ^ d ∉ x.asIdeal
    rw [Subsingleton.elim x (⊥ : PrimeSpectrum ℂ)]
    simpa using mul_ne_zero h (pow_ne_zero d (inv_ne_zero hi))

/-- The basic-open membership formula without fixing the selected standard coordinate chart. -/
lemma chartIntegralProj_preimage_basicOpen {n d : ℕ}
    (v : Projective.ComplexProjectiveSpace.CoordinateSpace n) (hv : v ≠ 0)
    (r : Projective.ComplexProjectiveSpace.UniversalRing n) (hd : 0 < d) (hr : r ∈ Projective.ComplexProjectiveSpace.UniversalGrading n d) :
    Projective.ComplexProjectiveSpace.chartIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (Projective.ComplexProjectiveSpace.UniversalGrading n) r =
      if Projective.ComplexProjectiveSpace.coordinateEvaluationHom v r = 0 then ⊥ else ⊤ := by
  let i := Projective.ComplexProjectiveSpace.coordinateIndex v hv
  let hi : v i ≠ 0 := Projective.ComplexProjectiveSpace.coordinateIndex_ne_zero v hv
  exact chartIntegralProjAt_preimage_basicOpen v i hi r hd hr

/-- The inverse image of a projective-spectrum basic open in complex projective space. -/
noncomputable def projectiveSpaceBasicOpen (n : ℕ) (r : Projective.ComplexProjectiveSpace.UniversalRing n) :
    (Foundations.ProjectiveSpaceIs.ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)).Opens :=
  Limits.pullback.snd
      (Limits.terminal.from (Spec ↧ℂ))
      (Limits.terminal.from (Proj (Projective.ComplexProjectiveSpace.UniversalGrading n))) ⁻¹ᵁ
    Proj.basicOpen (Projective.ComplexProjectiveSpace.UniversalGrading n) r

/-- A positive-degree basic open in complex projective space is affine. -/
lemma projectiveSpaceBasicOpen_isAffine {n d : ℕ}
    (r : Projective.ComplexProjectiveSpace.UniversalRing n) (hd : 0 < d) (hr : r ∈ Projective.ComplexProjectiveSpace.UniversalGrading n d) :
    IsAffine (projectiveSpaceBasicOpen n r).toScheme := by
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom)
      (Limits.terminal.from (Proj (Projective.ComplexProjectiveSpace.UniversalGrading n))) :=
    { of_isPullback := fun pb h ↦
        MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h }
  have hsnd : IsAffineHom (Limits.pullback.snd
      (Limits.terminal.from (Spec ↧ℂ))
      (Limits.terminal.from (Proj (Projective.ComplexProjectiveSpace.UniversalGrading n)))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact @IsAffineHom.isAffine_preimage _ _ _ hsnd
    (Proj.basicOpen (Projective.ComplexProjectiveSpace.UniversalGrading n) r)
    (Proj.isAffineOpen_basicOpen
      (𝒜 := Projective.ComplexProjectiveSpace.UniversalGrading n) (f := r) hr hd)

/-- A coordinate point lies in the projective-space basic open whenever the defining homogeneous
polynomial is nonzero on its coordinates. -/
lemma vectorToComplexPoint_mem_projectiveSpaceBasicOpen {n d : ℕ}
    (v : Projective.ComplexProjectiveSpace.CoordinateSpace n) (hv : v ≠ 0)
    (r : Projective.ComplexProjectiveSpace.UniversalRing n) (hd : 0 < d) (hr : r ∈ Projective.ComplexProjectiveSpace.UniversalGrading n d)
    (hne : Projective.ComplexProjectiveSpace.coordinateEvaluationHom v r ≠ 0) :
    Projective.ComplexProjectiveSpace.vectorToComplexPoint v hv ∈ Basic.Point.overOpen (projectiveSpaceBasicOpen n r) := by
  change ((Projective.ComplexProjectiveSpace.vectorToProjectiveSpace v hv) ≫ Limits.pullback.snd
    (Limits.terminal.from (Spec ↧ℂ))
    (Limits.terminal.from (Proj (Projective.ComplexProjectiveSpace.UniversalGrading n))))
      (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen (Projective.ComplexProjectiveSpace.UniversalGrading n) r
  rw [Projective.ComplexProjectiveSpace.vectorToProjectiveSpace_toProj]
  change IsLocalRing.closedPoint ℂ ∈
    Projective.ComplexProjectiveSpace.chartIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (Projective.ComplexProjectiveSpace.UniversalGrading n) r
  rw [chartIntegralProj_preimage_basicOpen v hv r hd hr, ite_eq_right hne]
  trivial

/-- Any two complex points of finite-dimensional projective space lie in a common affine open. -/
lemma projectiveSpace_pair_mem_affineOpen (n : ℕ)
    (z w : Basic.ComplexSchemePoint (Over.mk (Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :
    ∃ U : (Foundations.ProjectiveSpaceIs.ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ)).Opens,
      z ∈ Basic.Point.overOpen U ∧ w ∈ Basic.Point.overOpen U ∧ IsAffine U.toScheme := by
  obtain ⟨v, hvz⟩ := Projective.ComplexProjectiveSpace.surjective_vectorToComplexPoint z
  obtain ⟨u, huw⟩ := Projective.ComplexProjectiveSpace.surjective_vectorToComplexPoint w
  obtain ⟨r, hr, hrv, hru⟩ :=
    exists_common_nonvanishing_linearForm v.1 u.1 v.2 u.2
  refine ⟨projectiveSpaceBasicOpen n r, ?_, ?_,
    projectiveSpaceBasicOpen_isAffine r zero_lt_one hr⟩
  · rw [← hvz]
    exact vectorToComplexPoint_mem_projectiveSpaceBasicOpen
      v.1 v.2 r zero_lt_one hr hrv
  · rw [← huw]
    exact vectorToComplexPoint_mem_projectiveSpaceBasicOpen
      u.1 u.2 r zero_lt_one hr hru

/-- Finite-dimensional scheme-theoretic complex projective space is Hausdorff. -/
noncomputable instance instT2SpaceProjectiveSpaceComplexPoint (n : ℕ) :
    T2Space
      (Basic.ComplexSchemePoint (Over.mk (Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :=
  Basic.ComplexSchemePoint.t2Space_of_pair_mem_affineOpen
    (Over.mk (Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))
    (projectiveSpace_pair_mem_affineOpen n)

end ComplexPoint.ProjectiveHausdorff.ComplexProjectiveSpace

namespace ComplexPoint.ProjectiveHausdorff.ProjectiveSpace.Presentation

/-- Any two complex points of a projective presentation lie in a common affine open. -/
lemma pair_mem_affineOpen {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) (z w : Basic.ComplexSchemePoint (Over.mk f)) :
    ∃ U : X.Opens, z ∈ Basic.Point.overOpen U ∧
      w ∈ Basic.Point.overOpen U ∧ IsAffine U.toScheme := by
  obtain ⟨U, hzU, hwU, hUaff⟩ :=
    ComplexProjectiveSpace.projectiveSpace_pair_mem_affineOpen P.ambientDimension
      (ProjectiveCompact.ProjectiveSpace.Presentation.analyticImmersion P z) (ProjectiveCompact.ProjectiveSpace.Presentation.analyticImmersion P w)
  let : IsClosedImmersion P.immersion := P.isClosedImmersion
  let j := ProjectiveCompact.ProjectiveSpace.Presentation.overImmersion P
  refine ⟨P.immersion ⁻¹ᵁ U,
    (Basic.Point.mem_overOpen_map_iff j z U).mp hzU,
    (Basic.Point.mem_overOpen_map_iff j w U).mp hwU, ?_⟩
  exact @IsAffineHom.isAffine_preimage _ _ P.immersion inferInstance U hUaff

/-- The analytification of an explicit projective presentation is Hausdorff. -/
theorem complexPoint_t2Space {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    @T2Space (Basic.ComplexSchemePoint (Over.mk f)) Basic.Point.analyticTopology :=
  Basic.ComplexSchemePoint.t2Space_of_pair_mem_affineOpen (Over.mk f) (pair_mem_affineOpen P)

end ComplexPoint.ProjectiveHausdorff.ProjectiveSpace.Presentation

/-- The analytification of a projective complex scheme is Hausdorff. -/
noncomputable instance Foundations.ProjectiveSpaceIs.IsProjective.complexPoint_t2Space {X : Over (Spec ↧ℂ)}
    [h : Foundations.ProjectiveSpaceIs.IsProjective X.hom] : T2Space (ComplexPoint.Basic.ComplexSchemePoint X) :=
  ComplexPoint.ProjectiveHausdorff.ProjectiveSpace.Presentation.complexPoint_t2Space
    (Classical.choice h.nonempty_presentation)

end

end OAI.AlgebraicGeometry
