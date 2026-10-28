import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardInjective
import OAI.AlgebraicGeometry.Comparison.Betti.AugmentedComplexQuasiIso
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Pushforward Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardResolution.ModulePushforwardResolution

noncomputable section

/-! Local section exactness constructs the actual pushed injective resolution of a module sheaf. -/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite

variable (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y)
  {F : TopCat.Sheaf (ModuleCat R) X} (I : InjectiveResolution F)

def complex : CochainComplex (TopCat.Sheaf (ModuleCat R) Y) ℕ :=
  ((TopCat.Sheaf.pushforward (ModuleCat R) f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex

def augmentation : (TopCat.Sheaf.pushforward (ModuleCat R) f).obj F ⟶ (complex R f I).X 0 :=
  (TopCat.Sheaf.pushforward (ModuleCat R) f).map (I.ι.f 0)

theorem augmentation_comp : augmentation R f I ≫ (complex R f I).d 0 1 = 0 := by
  let G := TopCat.Sheaf.pushforward (ModuleCat R) f
  change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
  rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]

instance augmentation_mono : Mono (augmentation R f I) :=
  (TopCat.Sheaf.pushforward (ModuleCat R) f).map_mono (I.ι.f 0)

theorem augmentation_exact :
    (ShortComplex.mk (augmentation R f I) ((complex R f I).d 0 1)
      (augmentation_comp R f I)).Exact := by
  let G := TopCat.Sheaf.pushforward (ModuleCat R) f
  let S := ShortComplex.mk (I.ι.f 0) (I.cocomplex.d 0 1) I.ι_f_zero_comp_complex_d
  have hS : S.Exact := I.exact₀
  exact ShortComplex.exact_of_f_is_kernel (S.map G) (KernelFork.mapIsLimit _ hS.fIsKernel G)

def LocallyExact : Prop :=
  ∀ (V : Opens Y) (y : V), ∃ W : Opens Y, W ≤ V ∧ y.val ∈ W ∧
    ∀ n : ℕ, ∀ x : (I.cocomplex.X (n + 1)).obj.obj (op ((Opens.map f).obj W)),
      (I.cocomplex.d (n + 1) (n + 2)).hom.app (op ((Opens.map f).obj W)) x = 0 →
        ∃ z : (I.cocomplex.X n).obj.obj (op ((Opens.map f).obj W)),
          (I.cocomplex.d n (n + 1)).hom.app (op ((Opens.map f).obj W)) z = x

theorem exact_succ (hlocal : LocallyExact R f I) (n : ℕ) :
    (ShortComplex.mk ((complex R f I).d n (n + 1)) ((complex R f I).d (n + 1) (n + 2))
      ((complex R f I).d_comp_d n (n + 1) (n + 2))).Exact := by
  apply SheafLocalExactness.ModuleSheafLocalExactness.sheafExact_of_locally_exact_sections R
  intro V y
  obtain ⟨W, hWV, hyW, hW⟩ := hlocal V y
  exact ⟨W, hWV, hyW, hW n⟩

def resolution (hlocal : LocallyExact R f I) :
    InjectiveResolution ((TopCat.Sheaf.pushforward (ModuleCat R) f).obj F) where
  cocomplex := complex R f I
  injective n := (TopCat.Sheaf.pushforward (ModuleCat R) f).injective_obj_of_injective (I.injective n)
  ι := AlgebraicGeometry.Comparison.Betti.AugmentedComplexQuasiIso.Ext.nonnegativeAugmentation (complex R f I) (augmentation R f I) (augmentation_comp R f I)
  quasiIso := AlgebraicGeometry.Comparison.Betti.AugmentedComplexQuasiIso.Ext.nonnegativeAugmentation_quasiIso _ _ _
    (augmentation_exact R f I) (fun n => by
      exact (complex R f I).exactAt_iff' n (n + 1) (n + 2)
        (by simp) (by simp) |>.mpr (exact_succ R f I hlocal n))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.PushforwardResolution.ModulePushforwardResolution
