import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts
import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-! # Resolution Classes -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionClasses

noncomputable section

/-! Actual global cocycle representatives of sheaf Ext cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

abbrev sheafCohomologySource (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))

def sheafHomGlobalEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (sheafCohomologySource X ⟶ F) ≃+ F.obj.obj (op (⊤ : Opens X)) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

theorem sheafHomGlobalEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (φ : F ⟶ G) (f : sheafCohomologySource X ⟶ F) :
    sheafHomGlobalEquiv G (f ≫ φ) = φ.hom.app (op (⊤ : Opens X)) (sheafHomGlobalEquiv F f) := by
  rfl

variable {F : TopCat.Sheaf AddCommGrpCat.{0} X} (R : InjectiveResolution F)

def sheafResolutionCycleClass (n : ℕ)
    (s : (R.cocomplex.X n).obj.obj (op (⊤ : Opens X)))
    (hs : (R.cocomplex.d n (n + 1)).hom.app (op (⊤ : Opens X)) s = 0) :
    CategoryTheory.Sheaf.H F n :=
  R.extMk ((sheafHomGlobalEquiv (R.cocomplex.X n)).symm s) (n + 1) rfl (by
    apply (sheafHomGlobalEquiv (R.cocomplex.X (n + 1))).injective
    rw [sheafHomGlobalEquiv_naturality, AddEquiv.apply_symm_apply, map_zero]
    exact hs)

/-- Every actual sheaf cohomology class has a global cocycle in an injective resolution. -/
theorem exists_sheafResolutionCycle (n : ℕ) (a : CategoryTheory.Sheaf.H F n) :
    ∃ (s : (R.cocomplex.X n).obj.obj (op (⊤ : Opens X)))
      (hs : (R.cocomplex.d n (n + 1)).hom.app (op (⊤ : Opens X)) s = 0),
      sheafResolutionCycleClass R n s hs = a := by
  obtain ⟨f, hf, hfa⟩ := R.extMk_surjective a (n + 1) rfl
  have hs : (R.cocomplex.d n (n + 1)).hom.app (op (⊤ : Opens X))
      (sheafHomGlobalEquiv (R.cocomplex.X n) f) = 0 := by
    rw [← sheafHomGlobalEquiv_naturality, hf, map_zero]
  refine ⟨sheafHomGlobalEquiv (R.cocomplex.X n) f, hs, ?_⟩
  simpa only [sheafResolutionCycleClass, AddEquiv.symm_apply_apply] using hfa

/-- Vanishing means that this same global cocycle is an actual global coboundary. -/
theorem sheafResolutionCycleClass_eq_zero_iff (n : ℕ)
    (s : (R.cocomplex.X (n + 1)).obj.obj (op (⊤ : Opens X)))
    (hs : (R.cocomplex.d (n + 1) (n + 1 + 1)).hom.app (op (⊤ : Opens X)) s = 0) :
    sheafResolutionCycleClass R (n + 1) s hs = 0 ↔
      ∃ t : (R.cocomplex.X n).obj.obj (op (⊤ : Opens X)),
        (R.cocomplex.d n (n + 1)).hom.app (op (⊤ : Opens X)) t = s := by
  rw [sheafResolutionCycleClass, R.extMk_eq_zero_iff _ _ _ _ n rfl]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨sheafHomGlobalEquiv (R.cocomplex.X n) f, ?_⟩
    rw [← sheafHomGlobalEquiv_naturality, hf, AddEquiv.apply_symm_apply]
  · rintro ⟨t, ht⟩
    refine ⟨(sheafHomGlobalEquiv (R.cocomplex.X n)).symm t, ?_⟩
    apply (sheafHomGlobalEquiv (R.cocomplex.X (n + 1))).injective
    rw [sheafHomGlobalEquiv_naturality, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact ht

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionClasses
