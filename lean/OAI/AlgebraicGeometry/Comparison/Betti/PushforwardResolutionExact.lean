import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.LocalExactness
import OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveResolutionSections
import Mathlib.Topology.Sheaves.Functors

/-! # Pushforward Resolution Exact -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PushforwardResolutionExact.Cech

noncomputable section

/-! Acyclic inverse-image neighborhoods make the actual pushed injective resolution exact. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (F : TopCat.Sheaf AddCommGrpCat.{u} X)

def pushedInjectiveCocomplex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} Y) ℕ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ)).obj
    (injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)).cocomplex

def pushedInjectiveAugmentation : (TopCat.Sheaf.pushforward AddCommGrpCat f).obj F ⟶
    (pushedInjectiveCocomplex f F).X 0 :=
  (TopCat.Sheaf.pushforward AddCommGrpCat f).map
    ((injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)).ι.f 0)

theorem pushedInjectiveAugmentation_comp :
    pushedInjectiveAugmentation f F ≫ (pushedInjectiveCocomplex f F).d 0 1 = 0 := by
  let G := TopCat.Sheaf.pushforward AddCommGrpCat f
  let I : InjectiveResolution F := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
  change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
  erw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]

instance pushedInjectiveAugmentation_mono : Mono (pushedInjectiveAugmentation f F) := by
  let I : InjectiveResolution F := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
  let a : F ⟶ I.cocomplex.X 0 := I.ι.f 0
  have : Mono a := inferInstanceAs (Mono (I.ι.f 0))
  exact (TopCat.Sheaf.pushforward AddCommGrpCat f).map_mono a

theorem pushedInjectiveAugmentation_exact :
    (ShortComplex.mk (pushedInjectiveAugmentation f F) ((pushedInjectiveCocomplex f F).d 0 1)
      (pushedInjectiveAugmentation_comp f F)).Exact := by
  let G := TopCat.Sheaf.pushforward AddCommGrpCat f
  let I : InjectiveResolution F := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat X) :=
    ShortComplex.mk (I.ι.f 0) (I.cocomplex.d 0 1) I.ι_f_zero_comp_complex_d
  have hS : S.Exact := I.exact₀
  exact ShortComplex.exact_of_f_is_kernel (S.map G) (KernelFork.mapIsLimit _ hS.fIsKernel G)

theorem pushedInjectiveCocomplex_exact_succ
    (hlocal : ∀ (V : Opens Y) (y : V), ∃ W : Opens Y, W ≤ V ∧ y.val ∈ W ∧
      ∀ q, Subsingleton (Sheaf.H
        ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat ((Opens.map f).obj W).isOpenEmbedding).obj F) (q + 1)))
    (n : ℕ) :
    (ShortComplex.mk ((pushedInjectiveCocomplex f F).d n (n + 1))
      ((pushedInjectiveCocomplex f F).d (n + 1) (n + 2))
      ((pushedInjectiveCocomplex f F).d_comp_d n (n + 1) (n + 2))).Exact := by
  apply Betti.Sheaf.LocalExactness.Cech.sheafExact_of_locally_exact_sections
  intro V y
  obtain ⟨W, hWV, hyW, hW⟩ := hlocal V y
  refine ⟨W, hWV, hyW, ?_⟩
  exact SheafCohomology.Cech.InjectiveResolutionSections.TopCat.Sheaf.injectiveResolution_sections_exact_succ F ((Opens.map f).obj W) hW n

end

end OAI.AlgebraicGeometry.Comparison.Betti.PushforwardResolutionExact.Cech
