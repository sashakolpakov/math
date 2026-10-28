import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage
import OAI.AlgebraicGeometry.SheafCohomology.Cech.AcyclicResolution
import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict

/-! # Flasque Resolution Open Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueResolutionOpenSections

noncomputable section

/-! A flasque resolution is exact on sections of any open where its source has vanishing higher cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  (D : ResolutionExactImage.Data F) (hD : ∀ p, TopCat.Sheaf.IsFlasque (D.complex.X p)) (V : Opens X)

include hD

theorem flasqueResolution_openSections_exact_succ
    (hF : ∀ q, Subsingleton (Sheaf.H.{0}
      ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat V.isOpenEmbedding).obj F) (q + 1)))
    (n : ℕ) (x : (D.complex.X (n + 1)).obj.obj (op V))
    (hx : (D.complex.d (n + 1) (n + 2)).hom.app (op V) x = 0) :
    ∃ y : (D.complex.X n).obj.obj (op V), (D.complex.d n (n + 1)).hom.app (op V) y = x := by
  let R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} V.isOpenEmbedding
  have hRA : R.Additive := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict_additive V.isOpenEmbedding
  have hRL : PreservesFiniteLimits R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict_preservesFiniteLimits V.isOpenEmbedding
  have hRC : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let K := (R.mapHomologicalComplex (.up ℕ)).obj D.complex
  let e : R.obj F ⟶ K.X 0 := R.map D.augmentation
  have w : e ≫ K.d 0 1 = 0 := by
    change R.map D.augmentation ≫ R.map (D.complex.d 0 1) = 0
    rw [← R.map_comp, D.augmentation_d, R.map_zero]
  have hm : Mono e := R.map_mono D.augmentation
  have haug : (ShortComplex.mk e (K.d 0 1) w).Exact :=
    (ShortComplex.exact_of_f_is_kernel
      (ShortComplex.mk D.augmentation (D.complex.d 0 1) D.augmentation_d) D.isKernel).map R
  have hpos (q : ℕ) : (SheafCohomology.Cech.AcyclicResolution.Projective.resolutionDifferentialShortComplex K q).Exact := by
    have h := (D.complex.exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp)).mp (D.exact_succ q)
    exact h.map R
  have hK (p q : ℕ) : Subsingleton (Sheaf.H.{0} (K.X p) (q + 1)) := by
    have := hD p
    have hfl : TopCat.Sheaf.IsFlasque (K.X p) :=
      SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.IsFlasque.of_restrict _ (D.complex.X p) V.isOpenEmbedding
    exact SheafCohomology.Cech.Compat.TopCat.Sheaf.IsFlasque.subsingleton_H q
  have ht := SheafCohomology.Cech.AcyclicResolution.Projective.acyclicResolution_sections_exact_succ K e w haug hpos hF hK n
  change ∀ (x : (D.complex.X (n + 1)).obj.obj (op (V.isOpenEmbedding.functor.obj ⊤))),
    (D.complex.d (n + 1) (n + 2)).hom.app (op (V.isOpenEmbedding.functor.obj ⊤)) x = 0 →
    ∃ y : (D.complex.X n).obj.obj (op (V.isOpenEmbedding.functor.obj ⊤)),
      (D.complex.d n (n + 1)).hom.app (op (V.isOpenEmbedding.functor.obj ⊤)) y = x at ht
  rw [Opens.isOpenEmbedding_obj_top V] at ht
  exact ht x hx

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueResolutionOpenSections
