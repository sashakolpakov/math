import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicSheafResolution
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafRestriction
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Injective Resolution Section Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveResolutionSectionExactness.IntrinsicCech

noncomputable section

/-! An injective resolution is exact on sections over an acyclic open subset. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens X)

/-- Vanishing of all positive cohomology on an open makes sections of the
actual chosen injective resolution exact there in every positive degree. -/
theorem injectiveResolution_sections_exact_succ
    (hF : ∀ q, Subsingleton (CategoryTheory.Sheaf.H
      ((TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat V.isOpenEmbedding).obj F) (q + 1)))
    (n : ℕ)
    (x : ((injectiveResolution F).cocomplex.X (n + 1)).obj.obj (op V))
    (hx : ((injectiveResolution F).cocomplex.d
      (n + 1) (n + 2)).hom.app (op V) x = 0) :
    ∃ y : ((injectiveResolution F).cocomplex.X n).obj.obj (op V),
      ((injectiveResolution F).cocomplex.d n (n + 1)).hom.app (op V) y = x := by
  let I : InjectiveResolution F := injectiveResolution F
  let R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
        AddCommGrpCat.{u} := TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat.{u} V.isOpenEmbedding
  have : R.Additive := TopologicalSheafRestriction.IntrinsicCech.restrict_additive V.isOpenEmbedding
  have : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  have : PreservesFiniteLimits R := TopologicalSheafRestriction.IntrinsicCech.restrict_preservesFiniteLimits V.isOpenEmbedding
  have : PreservesColimits R :=
    (TopologicalSheafRestriction.IntrinsicCech.restrictPushforwardAdjunction AddCommGrpCat.{u} V.isOpenEmbedding).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits R := inferInstance
  let K := (R.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let e : R.obj F ⟶ K.X 0 := R.map (I.ι.f 0)
  have w : e ≫ K.d 0 1 = 0 := by
    change R.map (I.ι.f 0) ≫ R.map (I.cocomplex.d 0 1) = 0
    rw [← R.map_comp, I.ι_f_zero_comp_complex_d, R.map_zero]
  have : Mono e := by
    exact Functor.map_mono R (I.ι.f 0)
  have haug : (ShortComplex.mk e (K.d 0 1) w).Exact := I.exact₀.map R
  have hpos : ∀ q, (AcyclicSheafResolution.IntrinsicCech.resolutionDifferentialShortComplex K q).Exact := by
    intro q
    exact (I.exact_succ q).map R
  have hK (p q : ℕ) : Subsingleton (CategoryTheory.Sheaf.H (K.X p) (q + 1)) := by
    have : TopCat.Sheaf.IsFlasque (I.cocomplex.X p) :=
      @TopologicalSheafCohomology.IntrinsicCech.injectiveSheaf_flasque X (I.cocomplex.X p) (I.injective p)
    have : TopCat.Sheaf.IsFlasque (K.X p) :=
      TopologicalSheafRestriction.IntrinsicCech.flasque_of_restrict _ (I.cocomplex.X p) V.isOpenEmbedding
    exact TopologicalSheafCohomology.IntrinsicCech.flasqueSheaf_positiveCohomology_subsingleton (K.X p) q
  have ht := AcyclicSheafResolution.IntrinsicCech.acyclicResolution_sections_exact_succ
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

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InjectiveResolutionSectionExactness.IntrinsicCech
