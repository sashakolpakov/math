import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.Additive

/-! # Injective Augmentation Quasi -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveAugmentationQuasi.InjectiveAugmentation

noncomputable section

/-! # Additive images of resolutions of injective objects -/

open _root_.CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {A : C} [Injective A] (I : InjectiveResolution A) (G : C ⥤ D) [G.Additive]

/-- The actual resolution augmentation is the homotopy equivalence from
the trivial resolution of its injective source. -/
theorem homotopyEquiv_hom :
    (InjectiveResolution.homotopyEquiv (InjectiveResolution.self A) I).hom = I.ι := by
  exact (Category.id_comp _).symm.trans
    (InjectiveResolution.homotopyEquiv_hom_ι (InjectiveResolution.self A) I)

theorem map_quasiIso : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := by
  rw [← homotopyEquiv_hom I]
  exact (G.mapHomotopyEquiv
    (InjectiveResolution.homotopyEquiv (InjectiveResolution.self A) I)).quasiIso_hom

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveAugmentationQuasi.InjectiveAugmentation
