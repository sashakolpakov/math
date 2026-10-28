import OAI.AlgebraicGeometry.Foundations.Scheme.OpenImmersionPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalizationPointTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenLifts

/-! # Open Immersion -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion.SchemeComplexPoints

noncomputable section

/-!
# Open immersions on ordinary complex points

The carrier is the native type of relative scheme morphisms from `Spec ℂ`.
The point topology is the final topology of actual affine tests. Principal
localization neighborhoods provide the local lifts used below.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {U X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Local algebraic lifts through principal localizations imply openness of the
induced map on native complex points. -/
private theorem isOpenMap_of_localizationLifts
    (i : U ⟶ X) [IsOpenImmersion i.left]
    (hloc : ∀ (A : CommAlgCat ℂ) (g : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X)
      (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A), SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.map i) →
      ∃ a : A, x a ≠ 0 ∧ ∃ l : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Localization.Away a) ⟶ U,
        l ≫ i = Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
          (Algebra.algHom ℂ A (Localization.Away a)) ≫ g) :
    IsOpenMap (SchemePointHomeomorphs.schemeComplexPoints.map i) := by
  intro S hS
  apply (SchemePointHomeomorphs.schemeComplexPoints.isOpen_iff_affineTests _).mpr
  intro A g
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨y, hy, heq⟩ := hx
  obtain ⟨a, ha, l, hl⟩ := hloc A g x ⟨y, heq⟩
  let F : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a → SchemePointHomeomorphs.schemeComplexPoints U :=
    fun z => SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (Localization.Away a)) l
      ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph a).symm z)
  have hF : Continuous F :=
    (SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap (CommAlgCat.of ℂ (Localization.Away a)) l).comp
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph a).symm.continuous
  have hcomm (z : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a) :
      SchemePointHomeomorphs.schemeComplexPoints.map i (F z) = SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g z.val := by
    dsimp only [F]
    rw [← SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp, hl, SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap]
    have hz : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationRestriction a
        ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph a).symm z) = z.val := by
      rw [← Foundations.Scheme.AffineComplexPoints.affineComplexPoints.localizationPointHomeomorph_val,
        Homeomorph.apply_symm_apply]
    exact congrArg (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A g) hz
  let x' : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a := ⟨x, ha⟩
  have hx' : F x' ∈ S := by
    have hxy : F x' = y :=
      Foundations.Scheme.OpenImmersionPoints.openImmersion_complexPointMap_injective i ((hcomm x').trans heq.symm)
    rw [hxy]
    exact hy
  have hopen : IsOpen ((Subtype.val : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a →
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) '' (F ⁻¹' S)) :=
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpen_principalOpen a).isOpenEmbedding_subtypeVal.isOpenMap _
      (hS.preimage hF)
  have hmem : x ∈ ((Subtype.val : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a →
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) '' (F ⁻¹' S)) := ⟨x', hx', rfl⟩
  apply Filter.mem_of_superset (hopen.mem_nhds hmem)
  rintro z ⟨w, hw, rfl⟩
  exact ⟨F w, hw, hcomm w⟩

/-- An actual open immersion of complex schemes induces an open map on their
native complex-valued points with the ordinary affine-test topology. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_map_of_isOpenImmersion (i : U ⟶ X) [IsOpenImmersion i.left] :
    IsOpenMap (SchemePointHomeomorphs.schemeComplexPoints.map i) :=
  isOpenMap_of_localizationLifts i (SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift i)

/-- An actual open immersion induces an open embedding of ordinary complex
point spaces. Its local inverses come from genuine principal localizations. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (i : U ⟶ X) [IsOpenImmersion i.left] :
    Topology.IsOpenEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map i) :=
  .of_continuous_injective_isOpenMap (SchemePointHomeomorphs.schemeComplexPoints.continuous_map i)
    (Foundations.Scheme.OpenImmersionPoints.openImmersion_complexPointMap_injective i) (SchemePointHomeomorphs.schemeComplexPoints.isOpenMap_map_of_isOpenImmersion i)

/-- The image consists exactly of points whose underlying scheme point lies
in the open subscheme. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion (i : U ⟶ X) [IsOpenImmersion i.left] :
    Set.range (SchemePointHomeomorphs.schemeComplexPoints.map i) = SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range i.left := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨SchemePointHomeomorphs.schemeComplexPoints.underlying q, rfl⟩
  · intro hp
    have hsub : Set.range p.left ⊆ Set.range i.left := by
      rintro z ⟨t, rfl⟩
      have ht : t = SchemePointHomeomorphs.schemeComplexPoints.basePoint := by
        exact @Subsingleton.elim (PrimeSpectrum ℂ) inferInstance t SchemePointHomeomorphs.schemeComplexPoints.basePoint
      rw [ht]
      exact hp
    exact ⟨Foundations.Scheme.OpenImmersionPoints.openImmersion_relativeLift i p hsub, Foundations.Scheme.OpenImmersionPoints.openImmersion_relativeLift_fac i p hsub⟩

/-- Native points of an open subscheme are homeomorphic to the corresponding
ordinary open subset of the target point space. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph (i : U ⟶ X) [IsOpenImmersion i.left] :
    SchemePointHomeomorphs.schemeComplexPoints U ≃ₜ (SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Set.range i.left) :=
  (SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion i).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isOpenImmersion i))

@[simp]
theorem _root_.OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph_val (i : U ⟶ X) [IsOpenImmersion i.left]
    (p : SchemePointHomeomorphs.schemeComplexPoints U) :
    (SchemePointHomeomorphs.schemeComplexPoints.openImmersionPointHomeomorph i p).val = SchemePointHomeomorphs.schemeComplexPoints.map i p :=
  rfl

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.OpenImmersion.SchemeComplexPoints
