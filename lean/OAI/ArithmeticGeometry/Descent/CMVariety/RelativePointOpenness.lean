import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothRelativeNeighborhoods
import OAI.ArithmeticGeometry.Descent.CMVariety.ComposedSmoothCharts

/-! # Relative Point Openness -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

section

/-!
Product coordinates for actual smooth relative algebras. Smoothness
supplies the principal neighborhood and its finite presentation; the
constructed charts preserve the base projection and analytic evaluation
of every regular function.
-/

open scoped Classical ContDiff

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]

def SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.changeCoordinates
    {E E' F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A} {p : E → F}
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x p) (e : E ≃L[ℂ] E') :
    SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (p ∘ e.symm) where
  base := C.base
  total := C.total.transHomeomorph e.toHomeomorph
  basePoint := C.basePoint
  point := C.point
  mapsTo z hz := C.mapsTo (e.symm z) hz
  projection z hz := C.projection (e.symm z) hz
  regularTotal a :=
    (C.regularTotal a).comp (e.symm.contDiff.contDiffOn) (fun _ hz => hz)
  regularBase := C.regularBase

theorem RelativePointOpenness.Abelian.RelativeCharts.exists_smooth_relative_product_charts
    {I Sigma : Type} [Fintype I] [Fintype Sigma]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma)
    [Algebra.Smooth R A] (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    ∃ D : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.RelativePresentationAt (R := R) x,
      Nonempty (SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x
        (Prod.fst : (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ) ×
          (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates D.presentation.map → ℂ) → (AlgebraicGeometry.ComplexPoints.Analytic.JacobianRegularity.FreeCoordinates P.map → ℂ))) := by
  obtain ⟨D, ⟨C⟩⟩ := SmoothRelativeNeighborhoods.Abelian.RelativeCharts.exists_smooth_relative_point_charts P x
  let e := ComposedSmoothCharts.Abelian.RelativeCharts.productCoordinates P D.presentation
  have he : (ComposedSmoothCharts.Abelian.RelativeCharts.baseProjection P D.presentation : _ → _) ∘ e.symm = Prod.fst := by
    funext z
    rw [Function.comp_apply, ← ComposedSmoothCharts.Abelian.RelativeCharts.productCoordinates_fst]
    exact congrArg Prod.fst (e.apply_symm_apply z)
  refine ⟨D, ?_⟩
  rw [← he]
  exact ⟨C.changeCoordinates e⟩

end

/-!
The constructed relative product charts make the actual map on complex
points open. In particular, a neighborhood in an extended parameter maps
onto a neighborhood in the original parameter.
-/

open Set Filter
open scoped _root_.Topology Classical

theorem RelativePointOpenness.Abelian.RelativeCharts.image_mem_nhds_of_local_product
    {X Y E F : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace E] [TopologicalSpace F]
    (f : X → Y) (c : OpenPartialHomeomorph X (F × E))
    (b : OpenPartialHomeomorph Y F) (x : X)
    (hx : x ∈ c.source) (hfx : f x ∈ b.source)
    (hm : ∀ z ∈ c.target, f (c.symm z) ∈ b.source)
    (hp : ∀ z ∈ c.target, b (f (c.symm z)) = z.1)
    {U : Set X} (hU : U ∈ 𝓝 x) : f '' U ∈ 𝓝 (f x) := by
  let V := c.source ∩ U
  have hV : V ∈ 𝓝 x := inter_mem (c.open_source.mem_nhds hx) hU
  have hW : Prod.fst '' (c '' V) ∈ 𝓝 (c x).1 :=
    isOpenMap_fst.image_mem_nhds (c.image_mem_nhds hx hV)
  have hpx : b (f x) = (c x).1 := by
    simpa only [c.left_inv hx] using hp (c x) (c.map_source hx)
  rw [← hpx] at hW
  have hZ : b.symm '' (Prod.fst '' (c '' V)) ∈ 𝓝 (f x) := by
    simpa only [b.left_inv hfx] using b.symm.image_mem_nhds (b.map_source hfx) hW
  apply mem_of_superset hZ
  rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  have hmy : f y ∈ b.source := by
    simpa only [c.left_inv hy.1] using hm (c y) (c.map_source hy.1)
  have hpy : b (f y) = (c y).1 := by
    simpa only [c.left_inv hy.1] using hp (c y) (c.map_source hy.1)
  refine ⟨y, hy.2, ?_⟩
  rw [← hpy, b.left_inv hmy]

variable {R A : Type} [CommRing R] [Algebra ℂ R]
  [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]

theorem SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts.image_mem_nhds
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A}
    (C : SmoothRelativeNeighborhoods.Abelian.RelativeCharts.CompatibleRelativeCharts (R := R) x (Prod.fst : F × E → F))
    {U : Set (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)} (hU : U ∈ 𝓝 x) :
    (fun y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => y.comp (IsScalarTower.toAlgHom ℂ R A)) '' U ∈
      𝓝 (x.comp (IsScalarTower.toAlgHom ℂ R A)) :=
  RelativePointOpenness.Abelian.RelativeCharts.image_mem_nhds_of_local_product
    (fun y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => y.comp (IsScalarTower.toAlgHom ℂ R A))
    C.total C.base x C.point C.basePoint C.mapsTo C.projection hU

theorem RelativePointOpenness.Abelian.RelativeCharts.smooth_affine_point_image_mem_nhds
    {I Sigma : Type} [Fintype I] [Fintype Sigma]
    (P : Algebra.SubmersivePresentation ℂ R I Sigma) [Algebra.Smooth R A]
    (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) {U : Set (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)} (hU : U ∈ 𝓝 x) :
    (fun y : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => y.comp (IsScalarTower.toAlgHom ℂ R A)) '' U ∈
      𝓝 (x.comp (IsScalarTower.toAlgHom ℂ R A)) := by
  obtain ⟨D, ⟨C⟩⟩ := RelativePointOpenness.Abelian.RelativeCharts.exists_smooth_relative_product_charts P x
  exact C.image_mem_nhds hU

end

end OAI.ArithmeticGeometry.Descent.CMVariety
