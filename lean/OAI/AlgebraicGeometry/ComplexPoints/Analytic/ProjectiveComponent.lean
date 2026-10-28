import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyRealization
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover

/-! # Projective Component -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Analytic points of disjoint scheme decompositions

An actual disjoint family of open scheme inclusions covering the target gives
a homeomorphism from the topological sum of the native complex point spaces.
Applying this to the proved finite integral-component decomposition handles
all smooth projective presentations, including disconnected and empty ones.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

namespace ComplexPoints.Analytic

universe v

variable {ι : Type v} (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : ι → Over Foundations.Scheme.ProjectiveSpace.complexBase)
  (j : ∀ i, U i ⟶ X)

/-- The sum of the actual maps on native complex-valued points. -/
def SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap : (Σ i, SchemePointHomeomorphs.schemeComplexPoints (U i)) → SchemePointHomeomorphs.schemeComplexPoints X :=
  fun p => SchemePointHomeomorphs.schemeComplexPoints.map (j p.1) p.2

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap_mk (i : ι) (p : SchemePointHomeomorphs.schemeComplexPoints (U i)) :
    SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap X U j ⟨i, p⟩ = SchemePointHomeomorphs.schemeComplexPoints.map (j i) p := rfl

theorem SchemePointHomeomorphs.schemeComplexPoints.continuous_openFamilySigmaPointMap : Continuous (SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap X U j) :=
  continuous_sigma fun i => SchemePointHomeomorphs.schemeComplexPoints.continuous_map (j i)

variable [∀ i, IsOpenImmersion (j i).left]

theorem SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_openFamilySigmaPointMap : IsOpenMap (SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap X U j) :=
  isOpenMap_sigma.mpr fun i => SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_map_of_isOpenImmersion (j i)

/-- Scheme coverage supplies native-point coverage through the actual open-immersion lifts. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap_surjective
    (hcover : ∀ x : X.left, ∃ i, x ∈ Set.range (j i).left) :
    Function.Surjective (SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap X U j) := by
  intro p
  obtain ⟨i, hi⟩ := hcover (SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  have hp : p ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.map (j i)) := by
    rw [SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion]
    exact hi
  obtain ⟨q, hq⟩ := hp
  exact ⟨⟨i, q⟩, hq⟩

/-- Disjointness of the actual scheme ranges separates the sum's indices. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap_injective
    (hdisjoint : Pairwise (fun i k => Disjoint (Set.range (j i).left) (Set.range (j k).left))) :
    Function.Injective (SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap X U j) := by
  rintro ⟨i, p⟩ ⟨k, q⟩ h
  have hik : i = k := by
    by_contra hik
    have hpoint : SchemePointHomeomorphs.schemeComplexPoints.underlying (SchemePointHomeomorphs.schemeComplexPoints.map (j i) p) = SchemePointHomeomorphs.schemeComplexPoints.underlying (SchemePointHomeomorphs.schemeComplexPoints.map (j k) q) :=
      congrArg SchemePointHomeomorphs.schemeComplexPoints.underlying h
    exact Set.disjoint_left.mp (hdisjoint hik)
      (show SchemePointHomeomorphs.schemeComplexPoints.underlying (SchemePointHomeomorphs.schemeComplexPoints.map (j i) p) ∈ Set.range (j i).left from ⟨SchemePointHomeomorphs.schemeComplexPoints.underlying p, rfl⟩)
      (show SchemePointHomeomorphs.schemeComplexPoints.underlying (SchemePointHomeomorphs.schemeComplexPoints.map (j i) p) ∈ Set.range (j k).left from
        ⟨SchemePointHomeomorphs.schemeComplexPoints.underlying q, hpoint.symm⟩)
  subst k
  have hpq : p = q := (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (j i)).injective h
  subst q
  rfl

/-- Native points of a disjoint open decomposition are its actual topological sum. -/
def SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph
    (hcover : ∀ x : X.left, ∃ i, x ∈ Set.range (j i).left)
    (hdisjoint : Pairwise (fun i k => Disjoint (Set.range (j i).left) (Set.range (j k).left))) :
    (Σ i, SchemePointHomeomorphs.schemeComplexPoints (U i)) ≃ₜ SchemePointHomeomorphs.schemeComplexPoints X :=
  (Equiv.ofBijective (SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap X U j)
    ⟨SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap_injective X U j hdisjoint,
      SchemePointHomeomorphs.schemeComplexPoints.openFamilySigmaPointMap_surjective X U j hcover⟩).toHomeomorphOfContinuousOpen
    (SchemePointHomeomorphs.schemeComplexPoints.continuous_openFamilySigmaPointMap X U j) (SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_openFamilySigmaPointMap X U j)

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph_apply
    (hcover : ∀ x : X.left, ∃ i, x ∈ Set.range (j i).left)
    (hdisjoint : Pairwise (fun i k => Disjoint (Set.range (j i).left) (Set.range (j k).left)))
    (i : ι) (p : SchemePointHomeomorphs.schemeComplexPoints (U i)) :
    SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph X U j hcover hdisjoint ⟨i, p⟩ = SchemePointHomeomorphs.schemeComplexPoints.map (j i) p := rfl

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph_symm_map
    (hcover : ∀ x : X.left, ∃ i, x ∈ Set.range (j i).left)
    (hdisjoint : Pairwise (fun i k => Disjoint (Set.range (j i).left) (Set.range (j k).left)))
    (i : ι) (p : SchemePointHomeomorphs.schemeComplexPoints (U i)) :
    (SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph X U j hcover hdisjoint).symm (SchemePointHomeomorphs.schemeComplexPoints.map (j i) p) = ⟨i, p⟩ :=
  (SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph X U j hcover hdisjoint).symm_apply_apply ⟨i, p⟩

/-- In particular, a native disjoint open cover has exactly the sum topology on points. -/
def SchemePointHomeomorphs.schemeComplexPoints.disjointOpenCoverPointHomeomorph (𝒰 : Scheme.OpenCover.{v} X.left)
    (hdisjoint : Pairwise (fun i k => Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f k)))) :
    (Σ i, SchemePointHomeomorphs.schemeComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i)) ≃ₜ SchemePointHomeomorphs.schemeComplexPoints X :=
  SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph X (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰) (SchemePointHomeomorphs.schemeComplexPoints.openCoverInclusion X 𝒰)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩) hdisjoint

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.disjointOpenCoverPointHomeomorph_apply (𝒰 : Scheme.OpenCover.{v} X.left)
    (hdisjoint : Pairwise (fun i k => Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f k))))
    (p : Σ i, SchemePointHomeomorphs.schemeComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i)) :
    SchemePointHomeomorphs.schemeComplexPoints.disjointOpenCoverPointHomeomorph X 𝒰 hdisjoint p = SchemePointHomeomorphs.schemeComplexPoints.openCoverSigmaPointMap X 𝒰 p := rfl

end ComplexPoints.Analytic

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The actual component inclusion, as a morphism over the specified complex base. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentInclusionOver (C : irreducibleComponents P.carrier) :
    (P.componentVariety C).toOver ⟶ P.toOver :=
  Over.homMk (P.componentInclusion C) (P.componentInclusion_over C)

instance Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentInclusionOver_isOpenImmersion (C : irreducibleComponents P.carrier) :
    IsOpenImmersion (P.componentInclusionOver C).left :=
  P.componentInclusion_isOpenImmersion C

instance Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentInclusionOver_isClosedImmersion (C : irreducibleComponents P.carrier) :
    IsClosedImmersion (P.componentInclusionOver C).left :=
  P.componentInclusion_isClosedImmersion C

/-- The map from an actual integral component's analytic space. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPointMap (C : irreducibleComponents P.carrier) :
    (P.componentVariety C).analyticSpace → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.componentInclusionOver C)

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPointMap_range (C : irreducibleComponents P.carrier) :
    Set.range (P.componentPointMap C) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' C.val := by
  change Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.componentInclusionOver C)) = _
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion]
  have h : Set.range (P.componentInclusionOver C).left = C.val := P.componentInclusion_range C
  rw [h]

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentInclusions_cover (x : P.carrier) :
    ∃ C : irreducibleComponents P.carrier, x ∈ Set.range (P.componentInclusion C) := by
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  rw [P.componentInclusion_range]
  exact mem_irreducibleComponent

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentInclusions_pairwise_disjoint :
    Pairwise (fun C D : irreducibleComponents P.carrier =>
      Disjoint (Set.range (P.componentInclusion C)) (Set.range (P.componentInclusion D))) := by
  intro C D hCD
  exact TopologicalSpace.Opens.coe_disjoint.mpr
    (P.componentInclusionsOfStalkDomains_disjoint P.stalk_isDomain hCD)

/-- The analytic points of any smooth projective presentation are the finite
topological sum of its actual integral smooth projective components. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPointsHomeomorph :
    (Σ C : irreducibleComponents P.carrier, (P.componentVariety C).analyticSpace) ≃ₜ
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.disjointOpenFamilyPointHomeomorph P.toOver
    (fun C => (P.componentVariety C).toOver) P.componentInclusionOver
    P.componentInclusions_cover P.componentInclusions_pairwise_disjoint

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPointsHomeomorph_apply (C : irreducibleComponents P.carrier)
    (p : (P.componentVariety C).analyticSpace) :
    P.componentPointsHomeomorph ⟨C, p⟩ = P.componentPointMap C p := rfl

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPointsHomeomorph_symm_componentPointMap
    (C : irreducibleComponents P.carrier) (p : (P.componentVariety C).analyticSpace) :
    P.componentPointsHomeomorph.symm (P.componentPointMap C p) = ⟨C, p⟩ :=
  P.componentPointsHomeomorph.symm_apply_apply ⟨C, p⟩

end

end OAI.AlgebraicGeometry
