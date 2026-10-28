import OAI.AlgebraicGeometry.Albanese.Construction.SegreTensorChart
import OAI.AlgebraicGeometry.Albanese.Construction.SegreLocal

/-! # Segre Closed -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed

noncomputable section

section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

instance segreTensor_smooth (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Smooth (SegreTensorChart.segreTensorOver m n i j).hom := by
  have : IsIso (SegreTensorChart.segreTensorChartIso m n i j).inv.left :=
    (Over.forget _).map_isIso (SegreTensorChart.segreTensorChartIso m n i j).inv
  have h : Smooth ((SegreTensorChart.segreTensorChartIso m n i j).inv.left ≫ (SegreLocal.projectivePairChart m n (i, j)).hom) :=
    inferInstance
  rwa [(SegreTensorChart.segreTensorChartIso m n i j).inv.w] at h

instance segreTensor_reduced (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsReduced (SegreTensorChart.segreTensorOver m n i j).left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (SegreTensorChart.segreTensorOver m n i j).hom

/-- The affine Segre ring map as a morphism between the corresponding actual
affine schemes over the base. -/
def segreTensorToTargetChart (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreTensorChart.segreTensorOver m n i j ⟶ ProjectiveCover.polynomialChartOver (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (SegreAffineRing.segreAffineRingMap m n i j).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact (SegreAffineRing.segreAffineRingMap m n i j).commutes c)

/-- Dehomogenizing at the normalized tensor coordinate recovers every
tensor coordinate, including the coordinate equal to one. -/
theorem segreAffineRingMap_dehomogenize (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (k : Fin (SegreCoordinates.segreDimension m n + 1)) :
    SegreAffineRing.segreAffineRingMap m n i j (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (SegreCoordinates.segreIndexEquiv m n (i, j)) (MvPolynomial.X k)) =
      SegreCoordinates.segreVector (SegreAffineRing.segreTensorLeft m n i j) (SegreAffineRing.segreTensorRight m n i j) k := by
  classical
  by_cases hk : k = SegreCoordinates.segreIndexEquiv m n (i, j)
  · subst k
    simp [SegreAffineRing.segreTensorLeft, SegreAffineRing.segreTensorRight]
  · simp [Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize, Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne, hk, SegreAffineRing.segreAffineRingMap]

/-- Pulling back the target's normalized coordinate sections produces exactly
the tensor coordinate products as global regular functions. -/
theorem segreTensorToTargetChart_tuple (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (k : Fin (SegreCoordinates.segreDimension m n + 1)) :
    (segreTensorToTargetChart m n i j).left.appTop
        (AffineCoordinates.affineChartSections (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)) k) =
      (Scheme.ΓSpecIso (.of (SegreAffineRing.segreChartTensor m n i j))).inv
        (SegreCoordinates.segreVector (SegreAffineRing.segreTensorLeft m n i j) (SegreAffineRing.segreTensorRight m n i j) k) := by
  let φ := CommRingCat.ofHom (SegreAffineRing.segreAffineRingMap m n i j).toRingHom
  have h := Scheme.ΓSpecIso_inv_naturality φ
  have heval := congrArg (fun g : CommRingCat.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial (SegreCoordinates.segreDimension m n)
      (SegreCoordinates.segreIndexEquiv m n (i, j))) ⟶ Γ(Spec (.of (SegreAffineRing.segreChartTensor m n i j)), ⊤) =>
      g (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (SegreCoordinates.segreIndexEquiv m n (i, j)) (MvPolynomial.X k))) h
  change (Scheme.ΓSpecIso (.of (SegreAffineRing.segreChartTensor m n i j))).inv
      (SegreAffineRing.segreAffineRingMap m n i j (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize (SegreCoordinates.segreIndexEquiv m n (i, j)) (MvPolynomial.X k))) =
    (segreTensorToTargetChart m n i j).left.appTop
      (AffineCoordinates.affineChartSections (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)) k) at heval
  rw [segreAffineRingMap_dehomogenize] at heval
  exact heval.symm

set_option backward.isDefEq.respectTransparency false in
/-- The geometric Segre chart map is the spectrum of the explicit surjective
coordinate map, followed by the target affine-chart inclusion. -/
theorem segreChartMap_on_tensor (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (SegreTensorChart.segreTensorChartIso m n i j).inv ≫ SegreLocal.segreChartMap m n (i, j) =
      segreTensorToTargetChart m n i j ≫
        ProjectiveCover.polynomialChartOverMap (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)) := by
  rw [SegreLocal.segreChartMap_comp]
  apply Over.OverMorphism.ext
  change SegreCoordinates.segreMapOfCoordinates (SegreTensorChart.segreTensorOver m n i j).hom
    (SegreLocal.leftChartTuple (SegreTensorChart.segreTensorChartIso m n i j).inv) (SegreLocal.rightChartTuple (SegreTensorChart.segreTensorChartIso m n i j).inv)
    i j (SegreLocal.leftChartTuple_normalized _) (SegreLocal.rightChartTuple_normalized _) =
      (segreTensorToTargetChart m n i j).left ≫
        Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j))
  have hnat := ProjectiveCoordinates.projectiveMapOfCoordinates_comp (SegreTensorChart.segreTensorOver m n i j)
      (ProjectiveCover.polynomialChartOver (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)))
      (segreTensorToTargetChart m n i j)
      (AffineCoordinates.affineChartSections (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n (i, j)))
      (SegreCoordinates.segreIndexEquiv m n (i, j)) (AffineCoordinates.affineChartSections_self _ _)
  change (segreTensorToTargetChart m n i j).left ≫
      ProjectiveCoordinates.projectiveMapOfCoordinates (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase _ _)
        (AffineCoordinates.affineChartSections _ _) _ _ = _ at hnat
  rw [AffineCoordinates.projectiveMapOfCoordinates_affineChart] at hnat
  rw [hnat]
  unfold SegreCoordinates.segreMapOfCoordinates
  congr 1
  funext k
  rw [segreTensorToTargetChart_tuple]
  simp [SegreCoordinates.segreVector, SegreTensorChart.segreTensorChart_leftTuple, SegreTensorChart.segreTensorChart_rightTuple]

/-- The map between the actual affine tensor and target charts is a closed
immersion because its coordinate ring map was proved surjective. -/
theorem segreTensorToTargetChart_closed (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    IsClosedImmersion (segreTensorToTargetChart m n i j).left :=
  IsClosedImmersion.spec_of_surjective _ (SegreAffineRing.segreAffineRingMap_surjective m n i j)

end

section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

/-- The Segre map between the product chart and its target polynomial chart. -/
def segreSourceToTargetChart (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    SegreLocal.projectivePairChart m n ij ⟶
      ProjectiveCover.polynomialChartOver (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n ij) :=
  (SegreTensorChart.segreTensorChartIso m n ij.1 ij.2).hom ≫ segreTensorToTargetChart m n ij.1 ij.2

instance segreSourceToTargetChart_closed (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    IsClosedImmersion (segreSourceToTargetChart m n ij).left := by
  have : IsIso (SegreTensorChart.segreTensorChartIso m n ij.1 ij.2).hom.left :=
    (Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map_isIso (SegreTensorChart.segreTensorChartIso m n ij.1 ij.2).hom
  have := segreTensorToTargetChart_closed m n ij.1 ij.2
  change IsClosedImmersion ((SegreTensorChart.segreTensorChartIso m n ij.1 ij.2).hom.left ≫
    (segreTensorToTargetChart m n ij.1 ij.2).left)
  infer_instance

@[reassoc (attr := simp)]
theorem segreSourceToTargetChart_map (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    segreSourceToTargetChart m n ij ≫
        ProjectiveCover.polynomialChartOverMap (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n ij) =
      SegreLocal.segreChartMap m n ij := by
  rw [← cancel_epi (SegreTensorChart.segreTensorChartIso m n ij.1 ij.2).inv]
  simp only [segreSourceToTargetChart, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact (segreChartMap_on_tensor m n ij.1 ij.2).symm

set_option backward.isDefEq.respectTransparency false in
/-- The product chart is the full inverse image of the corresponding target
chart under the Segre map, including its scheme structure. -/
theorem segreChart_isPullback (m n : ℕ) (ij : Fin (m + 1) × Fin (n + 1)) :
    IsPullback (segreSourceToTargetChart m n ij).left (SegreLocal.projectivePairChartMap m n ij).left
      (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap (SegreCoordinates.segreDimension m n) (SegreCoordinates.segreIndexEquiv m n ij)) (SegreLocal.segreMap m n) := by
  apply IsOpenImmersion.isPullback
  · rw [SegreLocal.chartMap_segreMap]
    exact (congrArg Over.Hom.left (segreSourceToTargetChart_map m n ij)).symm
  · apply SetLike.coe_injective
    change (SegreLocal.segreMap m n) ⁻¹' Set.range (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap _ _) =
      Set.range (SegreLocal.projectivePairChartMap m n ij).left
    rw [SegreLocal.range_projectiveAffineChartMap]
    exact SegreLocal.segreMap_preimage_coordinate_range m n ij

set_option backward.isDefEq.respectTransparency false in
/-- The actual algebraic Segre morphism is a closed immersion, as checked
on the finite polynomial-chart cover of its target. -/
instance segreMap_closed (m n : ℕ) : IsClosedImmersion (SegreLocal.segreMap m n) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (ProjectiveCover.polynomialProjectiveCover (SegreCoordinates.segreDimension m n))]
  intro k
  change IsClosedImmersion (pullback.snd (SegreLocal.segreMap m n)
    (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap (SegreCoordinates.segreDimension m n) k))
  obtain ⟨ij, rfl⟩ := (SegreCoordinates.segreIndexEquiv m n).surjective k
  rw [← (segreChart_isPullback m n ij).flip.isoPullback_inv_snd]
  infer_instance

end

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

/-- The product of two closed projective embeddings is a closed immersion
into the actual product of the projective spaces. -/
theorem projective_tensorEmbedding_closed (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom) :
    IsClosedImmersion (P.toOverHom ⊗ₘ Q.toOverHom).left := by
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun _ _ hf hg => by let _ := hf; let _ := hg; infer_instance⟩
  rw [Over.tensorHom_left]
  have : IsClosedImmersion P.toOverHom.left := P.closedImmersion
  have : IsClosedImmersion Q.toOverHom.left := Q.closedImmersion
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (f := X.hom) (g := Y.hom)
    (f' := Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension)
    (g' := Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.ambientDimension)
    P.closedImmersion Q.closedImmersion P.over_base.symm Q.over_base.symm

/-- A genuine closed projective embedding for the tensor product, obtained
by composing the product embedding with the algebraic Segre immersion. -/
def tensorProjectivePresentation (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (X ⊗ Y).left (X ⊗ Y).hom where
  ambientDimension := SegreCoordinates.segreDimension P.ambientDimension Q.ambientDimension
  embedding := (P.toOverHom ⊗ₘ Q.toOverHom).left ≫ SegreLocal.segreMap P.ambientDimension Q.ambientDimension
  closedImmersion := by
    have := projective_tensorEmbedding_closed X Y P Q
    infer_instance
  over_base := by
    rw [Category.assoc, SegreLocal.segreMap_over]
    exact (P.toOverHom ⊗ₘ Q.toOverHom).w

/-- The actual scheme product of two smooth projective presentations,
equipped with the explicit Segre projective presentation. -/
abbrev tensorSmoothProjectivePresentation (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := (X.toOver ⊗ Y.toOver).left
  structureMap := (X.toOver ⊗ Y.toOver).hom
  projective := tensorProjectivePresentation X.toOver Y.toOver X.projective Y.projective
  smooth := by
    have : Smooth X.toOver.hom := X.smooth
    have : Smooth Y.toOver.hom := Y.smooth
    change Smooth (CategoryTheory.Limits.pullback.fst X.toOver.hom Y.toOver.hom ≫ X.toOver.hom)
    infer_instance

/-- The scheme product retains integrality over the algebraically closed
complex base. -/
abbrev tensorIntegralProjectiveVariety (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  ⟨tensorSmoothProjectivePresentation X.presentation Y.presentation, by
    have : IsIntegral X.toOver.left := X.property
    have : IsIntegral Y.toOver.left := Y.property
    have : Smooth X.toOver.hom := X.presentation.smooth
    have : Smooth Y.toOver.hom := Y.presentation.smooth
    exact Construction.Smooth.smooth_tensor_integral X.toOver Y.toOver⟩

/-- The product in the category of genuine projectively presented complex
abelian varieties. Its group operations are the native product operations. -/
def abelianProduct (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety where
  variety := tensorIntegralProjectiveVariety A.variety B.variety
  group := inferInstanceAs (GrpObj (A.toOver ⊗ B.toOver))
  commutative := inferInstanceAs (IsCommMonObj (A.toOver ⊗ B.toOver))

end

end OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed
