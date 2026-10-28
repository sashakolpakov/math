import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramFaithfulness

/-! # Diagram Schemes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth

noncomputable section

/-! A recovered algebra diagram gives actual smooth affine schemes and Cartesian recovery maps. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R] {I : Type v} {A : I → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable {J : Type w} {s t : J → I} {φ : ∀ j, A (s j) →ₐ[R] A (t j)}
variable (M : AffineDiagramModel.SmoothAffineDiagramModel R A s t φ)

def AffineDiagramModel.SmoothAffineDiagramModel.chartScheme (i : I) : Scheme.{u} := Spec (.of (M.algebra i))

def AffineDiagramModel.SmoothAffineDiagramModel.chartMap (i : I) : M.chartScheme i ⟶ Spec (.of M.coefficients) :=
  Spec.map (CommRingCat.ofHom (algebraMap M.coefficients (M.algebra i)))

instance AffineDiagramModel.SmoothAffineDiagramModel.chartMap_smooth (i : I) : Smooth (M.chartMap i) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.smooth_algebraMap.mpr (M.smooth i)

def AffineDiagramModel.SmoothAffineDiagramModel.chartArrow (j : J) : M.chartScheme (t j) ⟶ M.chartScheme (s j) :=
  Spec.map (CommRingCat.ofHom (M.arrow j).toRingHom)

instance AffineDiagramModel.SmoothAffineDiagramModel.chartArrow_open (j : J) : IsOpenImmersion (M.chartArrow j) := M.arrow_open j

theorem AffineDiagramModel.SmoothAffineDiagramModel.chartArrow_over (j : J) : M.chartArrow j ≫ M.chartMap (s j) = M.chartMap (t j) := by
  change Spec.map (CommRingCat.ofHom (M.arrow j).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap M.coefficients (M.algebra (s j)))) = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact (M.arrow j).commutes r

def AffineDiagramModel.SmoothAffineDiagramModel.realizationSpec (i : I) : Spec (.of (A i)) ⟶ M.chartScheme i :=
  Spec.map (CommRingCat.ofHom (M.realization i))

theorem AffineDiagramModel.SmoothAffineDiagramModel.realizationSpec_isPullback (i : I) :
    IsPullback (M.realizationSpec i) (Spec.map (CommRingCat.ofHom (algebraMap R (A i))))
      (M.chartMap i) (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)) :=
  Tensor.ModelCartesian.tensorModelMap_isPullback (M.recovery i)

theorem AffineDiagramModel.SmoothAffineDiagramModel.realizationSpec_natural (j : J) :
    M.realizationSpec (t j) ≫ M.chartArrow j =
      Spec.map (CommRingCat.ofHom (φ j).toRingHom) ≫ M.realizationSpec (s j) := by
  change Spec.map (CommRingCat.ofHom (M.realization (t j))) ≫
    Spec.map (CommRingCat.ofHom (M.arrow j).toRingHom) =
    Spec.map (CommRingCat.ofHom (φ j).toRingHom) ≫ Spec.map (CommRingCat.ofHom (M.realization (s j)))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (M.realization_arrow j))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth
