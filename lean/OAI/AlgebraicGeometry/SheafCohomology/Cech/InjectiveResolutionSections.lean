import OAI.AlgebraicGeometry.SheafCohomology.Cech.AcyclicResolution
import OAI.AlgebraicGeometry.SheafCohomology.Cech.TopCatRestrict
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Injective Resolution Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveResolutionSections.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! An injective resolution is exact on sections over an acyclic open subset. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X)

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of all positive cohomology on an open makes sections of the
actual chosen injective resolution exact there in every positive degree. -/
theorem injectiveResolution_sections_exact_succ
    (hF : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
      ((TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat V.isOpenEmbedding).obj F) (q + 1)))
    (n : ℕ)
    (x : ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex.X (n + 1)).obj.obj (op V))
    (hx : ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex.d
      (n + 1) (n + 2)).hom.app (op V) x = 0) :
    ∃ y : ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex.X n).obj.obj (op V),
      ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex.d n (n + 1)).hom.app (op V) y = x := by
  let I := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)
  let R := TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{u} V.isOpenEmbedding
  have : R.Additive := TopCatRestrict.TopCat.Sheaf.restrict_additive V.isOpenEmbedding
  have : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  have : PreservesFiniteLimits R := TopCatRestrict.TopCat.Sheaf.restrict_preservesFiniteLimits V.isOpenEmbedding
  have : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let K := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e : R.obj (Compat.TopCat.Sheaf.toSiteSheaf F) ⟶ K.X 0 := R.map (I.ι.f 0)
  have w : e ≫ K.d 0 1 = 0 := by
    change R.map (I.ι.f 0) ≫ R.map (I.cocomplex.d 0 1) = 0
    rw [← R.map_comp, I.ι_f_zero_comp_complex_d, R.map_zero]
  have : Mono e := by dsimp [e]; infer_instance
  have haug : (ShortComplex.mk e (K.d 0 1) w).Exact := I.exact₀.map R
  have hpos : ∀ q, (AcyclicResolution.Projective.resolutionDifferentialShortComplex K q).Exact := by
    intro q
    exact (I.exact_succ q).map R
  have hK (p q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)) := by
    have : IsFlasque (I.cocomplex.X p) :=
      @Compat.TopCat.Sheaf.IsFlasque.of_injective X (I.cocomplex.X p) (I.injective p)
    have : IsFlasque (K.X p) :=
      TopCatRestrict.TopCat.Sheaf.IsFlasque.of_restrict _ (I.cocomplex.X p) V.isOpenEmbedding
    exact Compat.TopCat.Sheaf.IsFlasque.subsingleton_H q
  have ht := AcyclicResolution.Projective.acyclicResolution_sections_exact_succ
    K e w haug hpos hF hK n
  change ∀ (x : (I.cocomplex.X (n + 1)).obj.obj
      (op (V.isOpenEmbedding.functor.obj ⊤))),
    (I.cocomplex.d (n + 1) (n + 2)).hom.app
      (op (V.isOpenEmbedding.functor.obj ⊤)) x = 0 →
    ∃ y : (I.cocomplex.X n).obj.obj (op (V.isOpenEmbedding.functor.obj ⊤)),
      (I.cocomplex.d n (n + 1)).hom.app
        (op (V.isOpenEmbedding.functor.obj ⊤)) y = x at ht
  rw [Opens.isOpenEmbedding_obj_top V] at ht
  exact ht x hx

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveResolutionSections.TopCat.Sheaf
