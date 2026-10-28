import OAI.AlgebraicGeometry.AbelianVariety.AnalyticGroup
import OAI.AlgebraicGeometry.AbelianVariety.PowerLie
import OAI.AlgebraicGeometry.Albanese.Construction.GeneratedClosed
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop
import OAI.AlgebraicGeometry.Betti.ProjectiveCohomology
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveMaps

/-! # Power Image -/

namespace OAI.AlgebraicGeometry.AbelianVariety.PowerImage.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

def abelianPowerMorphism (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) : A.toOver ⟶ A.toOver :=
  (𝟙 A.toOver) ^ n

theorem abelianPowerMorphism_point (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    x ≫ abelianPowerMorphism A n = x ^ n := by
  rw [abelianPowerMorphism, MonObj.comp_pow, Category.comp_id]

instance abelianPowerMorphism_isProper (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    IsProper (abelianPowerMorphism A n).left := by
  have : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  have : IsProper ((abelianPowerMorphism A n).left ≫ A.toOver.hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp _ A.toOver.hom

def abelianPowerSupport (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) : IrreducibleCloseds A.carrier where
  carrier := Set.range (abelianPowerMorphism A n).left
  isIrreducible' := by
    let : IsIntegral A.toOver.left := A.variety.property
    change IsIrreducible (Set.range (abelianPowerMorphism A n).left : Set A.toOver.left)
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ A.toOver.left).image (abelianPowerMorphism A n).left
        (abelianPowerMorphism A n).left.continuous.continuousOn)
  isClosed' := (abelianPowerMorphism A n).left.isClosedMap.isClosed_range

def abelianPowerPointSubgroup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Subgroup (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) := (powMonoidHom n).range

theorem abelianPowerSupport_point (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) :
    q.left (IsLocalRing.closedPoint ℂ) ∈ abelianPowerSupport A n ↔
      q ∈ abelianPowerPointSubgroup A n := by
  let : LocallyOfFiniteType A.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType A.variety.structureMap)
  have h := Albanese.Construction.ClosedPoints.pointMap_range_iff A.toOver A.toOver (abelianPowerMorphism A n) q
  change (∃ p, p ≫ abelianPowerMorphism A n = q) ↔
    q.left (IsLocalRing.closedPoint ℂ) ∈ abelianPowerSupport A n at h
  rw [← h]
  simp only [abelianPowerMorphism_point, abelianPowerPointSubgroup, MonoidHom.mem_range,
    powMonoidHom_apply]

theorem abelianPowerSupport_smooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Smooth (CycleClass.Geometric.SupportFiniteType.supportStructureMap (abelianPowerSupport A n) A.variety.structureMap) := by
  let Z := abelianPowerSupport A n
  let W : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z A.variety.structureMap)
  let i : W ⟶ A.toOver := Over.homMk (CycleClass.Geometric.GenericPoint.reducedSupportι Z) rfl
  let : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι Z))
  let : IsIntegral W.left := inferInstanceAs (IsIntegral (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z))
  let : LocallyOfFiniteType W.hom :=
    inferInstanceAs (LocallyOfFiniteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z A.variety.structureMap))
  let : LocallyOfFiniteType A.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType A.variety.structureMap)
  apply Albanese.Construction.SubgroupScheme.closed_point_subgroup_smooth W A.toOver i (abelianPowerPointSubgroup A n)
  intro q
  rw [Albanese.Construction.ClosedPoints.pointMap_range_iff W A.toOver i q]
  change q.left (IsLocalRing.closedPoint ℂ) ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι Z) ↔ _
  rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact abelianPowerSupport_point A n q

def abelianPowerImageVariety (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  ⟨{ carrier := CycleClass.Geometric.GenericPoint.reducedSupportScheme (abelianPowerSupport A n)
     structureMap := CycleClass.Geometric.SupportFiniteType.supportStructureMap (abelianPowerSupport A n) A.variety.structureMap
     projective := A.variety.presentation.projective.reducedSupport (abelianPowerSupport A n)
     smooth := abelianPowerSupport_smooth A n }, inferInstance⟩

def abelianPowerImageInclusion (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (abelianPowerImageVariety A n).toOver ⟶ A.toOver :=
  Over.homMk (CycleClass.Geometric.GenericPoint.reducedSupportι (abelianPowerSupport A n)) rfl

instance abelianPowerImageInclusion_isClosedImmersion (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    IsClosedImmersion (abelianPowerImageInclusion A n).left :=
  inferInstanceAs (IsClosedImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι (abelianPowerSupport A n)))

theorem abelianPowerMorphism_range_subset (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Set.range (abelianPowerMorphism A n).left ⊆ Set.range (abelianPowerImageInclusion A n).left := by
  change Set.range (abelianPowerMorphism A n).left ⊆
    Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (abelianPowerSupport A n))
  intro x hx
  exact (Set.ext_iff.mp (CycleClass.Geometric.GenericPoint.range_reducedSupportι (abelianPowerSupport A n)) x).mpr hx

def abelianPowerImageFactor (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    A.toOver ⟶ (abelianPowerImageVariety A n).toOver := by
  let : IsIntegral A.toOver.left := A.variety.property
  exact Albanese.Construction.GeneratedClosed.closedFactorOver (abelianPowerImageVariety A n).toOver A.toOver A.toOver
    (abelianPowerImageInclusion A n) (abelianPowerMorphism A n)
    (abelianPowerMorphism_range_subset A n)

theorem abelianPowerImageFactor_comp (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    abelianPowerImageFactor A n ≫ abelianPowerImageInclusion A n = abelianPowerMorphism A n := by
  let : IsIntegral A.toOver.left := A.variety.property
  exact Albanese.Construction.GeneratedClosed.closedFactorOver_comp (abelianPowerImageVariety A n).toOver A.toOver A.toOver
    (abelianPowerImageInclusion A n) (abelianPowerMorphism A n)
    (abelianPowerMorphism_range_subset A n)

theorem abelianPowerImage_dimension (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (abelianPowerImageVariety A n).complexDimension =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (abelianPowerSupport A n) A.variety.structureMap :=
  (abelianPowerImageVariety A n).complexDimension_eq_transcendenceDimension

theorem abelianPowerImage_dimension_ge (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) (hn : n ≠ 0) :
    A.variety.complexDimension ≤ (abelianPowerImageVariety A n).complexDimension := by
  let W := abelianPowerImageVariety A n
  let b := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (abelianPowerImageFactor A n)
  let j := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (abelianPowerImageInclusion A n)
  have hb : ContMDiff 𝓘(ℝ, A.variety.analyticModel) 𝓘(ℝ, W.analyticModel) ∞ b :=
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map (V := A.variety) (W := W)
      (abelianPowerImageFactor A n) ∞
  have hj : ContMDiff 𝓘(ℝ, W.analyticModel) 𝓘(ℝ, A.variety.analyticModel) ∞ j :=
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map (V := W) (W := A.variety)
      (abelianPowerImageInclusion A n) ∞
  have he : j ∘ b = (fun x : A.variety.analyticSpace => x ^ n) := by
    funext x
    change (x ≫ abelianPowerImageFactor A n) ≫ abelianPowerImageInclusion A n = x ^ n
    rw [Category.assoc, abelianPowerImageFactor_comp, abelianPowerMorphism_point]
  have hd := mfderiv_comp (I := 𝓘(ℝ, A.variety.analyticModel)) (I' := 𝓘(ℝ, W.analyticModel))
    (I'' := 𝓘(ℝ, A.variety.analyticModel)) (1 : A.variety.analyticSpace)
    (hj.mdifferentiableAt (by simp)) (hb.mdifferentiableAt (by simp))
  rw [he] at hd
  let L : A.variety.analyticModel →L[ℝ] W.analyticModel :=
    mfderiv 𝓘(ℝ, A.variety.analyticModel) 𝓘(ℝ, W.analyticModel) b 1
  have hL : Function.Injective L := by
    intro v w h
    apply PowerLie.Constructions.ExteriorCohomology.mfderiv_pow_one_injective (E := A.variety.analyticModel) (G := A.variety.analyticSpace) n hn
    have hv := congrArg (fun f : A.variety.analyticModel →L[ℝ] A.variety.analyticModel => f v) hd
    have hw := congrArg (fun f : A.variety.analyticModel →L[ℝ] A.variety.analyticModel => f w) hd
    exact hv.trans ((congrArg
      (mfderiv 𝓘(ℝ, W.analyticModel) 𝓘(ℝ, A.variety.analyticModel) j (b 1)) h).trans hw.symm)
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := L.toLinearMap) hL
  rw [A.variety.analyticModel_real_finrank, W.analyticModel_real_finrank] at hdim
  change A.variety.complexDimension ≤ W.complexDimension
  omega

theorem abelianPowerSupport_eq_univ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) (hn : n ≠ 0) :
    (abelianPowerSupport A n : Set A.carrier) = Set.univ := by
  let Z : IrreducibleCloseds A.carrier :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ A.carrier, isClosed_univ⟩
  have he : abelianPowerSupport A n = Z := by
    by_contra hne
    have hlt : abelianPowerSupport A n < Z :=
      lt_of_le_of_ne (Set.subset_univ _) hne
    have hdrop := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt
      (abelianPowerSupport A n) Z A.variety.structureMap hlt
    have htop := Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le Z A.variety.structureMap
    have hdim := abelianPowerImage_dimension_ge A n hn
    rw [abelianPowerImage_dimension] at hdim
    rw [← A.variety.complexDimension_eq_transcendenceDimension] at htop
    omega
  exact congrArg (fun W : IrreducibleCloseds A.carrier => (W : Set A.carrier)) he

theorem abelianPoint_pow_surjective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x : A.variety.analyticSpace => x ^ n) := by
  intro q
  have hq : q.left (IsLocalRing.closedPoint ℂ) ∈ abelianPowerSupport A n := by
    exact (Set.ext_iff.mp (abelianPowerSupport_eq_univ A n hn)
      (q.left (IsLocalRing.closedPoint ℂ))).mpr (Set.mem_univ _)
  have hp := (abelianPowerSupport_point A n q).mp hq
  exact hp

theorem abelianPoint_connectedSpace (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ConnectedSpace A.variety.analyticSpace := by
  let : LocallyConnectedSpace A.variety.analyticSpace :=
    ChartedSpace.locallyConnectedSpace A.variety.analyticModel A.variety.analyticSpace
  exact PowerLie.Constructions.ExteriorCohomology.connectedSpace_of_surjective_positive_powers (abelianPoint_pow_surjective A)

end

end OAI.AlgebraicGeometry.AbelianVariety.PowerImage.Constructions.ExteriorCohomology
