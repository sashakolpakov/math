import OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Maps.OpenQuotient

/-! # Scheme Affine Cover -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Native scheme open covers on ordinary complex points

Every native scheme open cover induces an actual open cover of its complex
points. Its disjoint-union map is an open quotient map, so the ordinary point
topology is exactly the topology obtained by gluing the chosen cover. In
particular this applies to mathlib's canonical affine cover without any extra
point-coverage hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe v

/-- A member of a native scheme open cover, with the inherited complex structure map. -/
def SchemePointHomeomorphs.schemeComplexPoints.openCoverObject (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (𝒰 : Scheme.OpenCover.{v} X.left)
    (i : 𝒰.I₀) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (𝒰.f i ≫ X.hom)

/-- The actual relative open immersion of a cover member into the original scheme. -/
def SchemePointHomeomorphs.schemeComplexPoints.openCoverInclusion (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (𝒰 : Scheme.OpenCover.{v} X.left)
    (i : 𝒰.I₀) : SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i ⟶ X :=
  Over.homMk (𝒰.f i) rfl

instance SchemePointHomeomorphs.schemeComplexPoints.isOpenImmersion_openCoverInclusion (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (𝒰 : Scheme.OpenCover.{v} X.left) (i : 𝒰.I₀) :
    IsOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.openCoverInclusion X 𝒰 i).left := by
  change IsOpenImmersion (𝒰.f i)
  infer_instance

/-- The induced map from the native complex points of one cover member. -/
def SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (𝒰 : Scheme.OpenCover.{v} X.left)
    (i : 𝒰.I₀) : SchemePointHomeomorphs.schemeComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i) → SchemePointHomeomorphs.schemeComplexPoints X :=
  SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.openCoverInclusion X 𝒰 i)

/-- Native scheme coverage implies coverage of complex-valued points, by the
proved lifting property of open immersions. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.exists_openCoverPoint_lift (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (𝒰 : Scheme.OpenCover.{v} X.left) (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ i, ∃ q : SchemePointHomeomorphs.schemeComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i),
      SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 i q = p := by
  let i := 𝒰.idx (SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  have hp : p ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.openCoverInclusion X 𝒰 i)) := by
    rw [SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion]
    exact 𝒰.covers (SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  obtain ⟨q, hq⟩ := hp
  exact ⟨i, q, hq⟩

/-- Each map in the induced cover is an open embedding for the ordinary topology. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_openCoverPointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (𝒰 : Scheme.OpenCover.{v} X.left) (i : 𝒰.I₀) :
    Topology.IsOpenEmbedding (SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 i) :=
  SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.openCoverInclusion X 𝒰 i)

/-- The induced cover really covers every complex-valued point. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.iUnion_range_openCoverPointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (𝒰 : Scheme.OpenCover.{v} X.left) :
    (⋃ i, Set.range (SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 i)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨i, q, hq⟩ := SchemePointHomeomorphs.schemeComplexPoints.exists_openCoverPoint_lift X 𝒰 p
  exact Set.mem_iUnion.mpr ⟨i, q, hq⟩

/-- The disjoint union of the native complex point spaces of a native open cover. -/
def SchemePointHomeomorphs.schemeComplexPoints.openCoverSigmaPointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (𝒰 : Scheme.OpenCover.{v} X.left) :
    (Σ i, SchemePointHomeomorphs.schemeComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X 𝒰 i)) → SchemePointHomeomorphs.schemeComplexPoints X :=
  fun p => SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 p.1 p.2

/-- The map from the disjoint union of cover members is an open quotient map. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isOpenQuotientMap_openCoverSigmaPointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (𝒰 : Scheme.OpenCover.{v} X.left) :
    IsOpenQuotientMap (SchemePointHomeomorphs.schemeComplexPoints.openCoverSigmaPointMap X 𝒰) where
  surjective p := by
    obtain ⟨i, q, hq⟩ := SchemePointHomeomorphs.schemeComplexPoints.exists_openCoverPoint_lift X 𝒰 p
    exact ⟨⟨i, q⟩, hq⟩
  continuous := continuous_sigma fun i =>
    (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_openCoverPointMap X 𝒰 i).continuous
  isOpenMap := isOpenMap_sigma.mpr fun i =>
    (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_openCoverPointMap X 𝒰 i).isOpenMap

/-- Openness is detected on any native scheme open cover. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isOpen_iff_openCover (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (𝒰 : Scheme.OpenCover.{v} X.left)
    (S : Set (SchemePointHomeomorphs.schemeComplexPoints X)) :
    IsOpen S ↔ ∀ i, IsOpen (SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 i ⁻¹' S) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isOpenQuotientMap_openCoverSigmaPointMap X 𝒰).isQuotientMap.isCoinducing.isOpen_preimage.symm.trans
    isOpen_sigma_iff

/-- Continuity is detected on any chosen native scheme open cover. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_openCover (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (𝒰 : Scheme.OpenCover.{v} X.left)
    {T : Type*} [TopologicalSpace T] (F : SchemePointHomeomorphs.schemeComplexPoints X → T) :
    Continuous F ↔ ∀ i, Continuous (F ∘ SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 i) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isOpenQuotientMap_openCoverSigmaPointMap X 𝒰).isQuotientMap.continuous_iff.trans
    continuous_sigma_iff

/-- The final affine-test topology is exactly the topology obtained by gluing
any native open cover, including the canonical affine cover. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.analyticTopology_eq_openCover (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (𝒰 : Scheme.OpenCover.{v} X.left) :
    SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X =
      ⨆ i, TopologicalSpace.coinduced (SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 i) inferInstance := by
  apply TopologicalSpace.ext_iff.mpr
  intro S
  change IsOpen S ↔ _
  exact (SchemePointHomeomorphs.schemeComplexPoints.isOpen_iff_openCover X 𝒰 S).trans
    (isOpen_iSup_iff (t := fun i =>
      TopologicalSpace.coinduced (SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X 𝒰 i) inferInstance)).symm

/-- Members of the canonical cover retain their genuine affine scheme structure. -/
instance SchemePointHomeomorphs.schemeComplexPoints.isAffine_openCoverObject_affineCover (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (i : X.left.affineCover.I₀) :
    IsAffine (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X X.left.affineCover i).left := by
  change IsAffine (X.left.affineCover.X i)
  infer_instance

/-- The canonical affine cover detects continuity on ordinary complex points. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineCover (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    {T : Type*} [TopologicalSpace T] (F : SchemePointHomeomorphs.schemeComplexPoints X → T) :
    Continuous F ↔ ∀ i, Continuous (F ∘ SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X X.left.affineCover i) :=
  SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_openCover X X.left.affineCover F

/-- The actual algebra of sections on an open set, with scalars induced by
the given structure morphism to the complex base. -/
def SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens) : CommAlgCat ℂ := by
  letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
  exact CommAlgCat.of ℂ Γ(X.left, U)

/-- The canonical spectrum-of-sections map of an affine open, as a morphism
over the complex base. -/
def SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens)
    (hU : IsAffineOpen U) : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) ⟶ X := by
  refine Over.homMk hU.fromSpec ?_
  change hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap X.hom U))
  exact (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec X.hom U hU).symm

instance SchemePointHomeomorphs.schemeComplexPoints.isOpenImmersion_affineOpenSchemeMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens)
    (hU : IsAffineOpen U) : IsOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU).left := by
  change IsOpenImmersion hU.fromSpec
  infer_instance

/-- The canonical map from characters of an affine open's actual section
algebra to global complex-valued scheme points. -/
def SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens)
    (hU : IsAffineOpen U) : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) → SchemePointHomeomorphs.schemeComplexPoints X :=
  SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)

/-- The spectrum-of-sections chart is an open embedding in the ordinary topology. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_affineOpenPointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens)
    (hU : IsAffineOpen U) : Topology.IsOpenEmbedding (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)).comp
    (SchemePointHomeomorphs.affineSchemePointHomeomorph (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)).isOpenEmbedding

/-- The actual section-algebra chart has exactly the expected affine-open point image. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (U : X.left.Opens)
    (hU : IsAffineOpen U) :
    Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) = SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (U : Set X.left) := by
  have hr : Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) =
      Set.range (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU)) := by
    change Set.range (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) ∘
      SchemePointHomeomorphs.affineSchemePointEquiv (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) = _
    rw [Set.range_comp, (SchemePointHomeomorphs.affineSchemePointEquiv (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)).surjective.range_eq,
      Set.image_univ]
  rw [hr, SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion]
  change SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range hU.fromSpec = _
  rw [hU.range_fromSpec]

/-- Every native complex point has coordinates in the actual section algebra
of an affine open from the canonical scheme cover. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ U : X.left.Opens, ∃ hU : IsAffineOpen U,
      ∃ x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U),
        SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x = p := by
  let i := X.left.affineCover.idx (SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  let U : X.left.Opens := (X.left.affineCover.f i).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.left.affineCover.f i)
  have hp : p ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := by
    rw [SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap]
    exact X.left.affineCover.covers (SchemePointHomeomorphs.schemeComplexPoints.underlying p)
  obtain ⟨x, hx⟩ := hp
  exact ⟨U, hU, x, hx⟩

/-- The chosen canonical affine cover tests continuity directly on the
ordinary character spaces of its actual global-section algebras. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineCoverGamma (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    {T : Type*} [TopologicalSpace T] (F : SchemePointHomeomorphs.schemeComplexPoints X → T) :
    Continuous F ↔ ∀ i, Continuous
      (F ∘ SchemePointHomeomorphs.schemeComplexPoints.openCoverPointMap X X.left.affineCover i ∘
        (AffineSchemePointTopology.affineNativePointHomeomorph (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X X.left.affineCover i)).symm) := by
  rw [SchemePointHomeomorphs.schemeComplexPoints.continuous_iff_affineCover X F]
  apply forall_congr'
  intro i
  exact (AffineSchemePointTopology.affineNativePointHomeomorph
    (SchemePointHomeomorphs.schemeComplexPoints.openCoverObject X X.left.affineCover i)).symm.comp_continuous_iff'.symm

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
