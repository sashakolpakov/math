import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors

/-! # Composite Kernel Square -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositeKernelSquare

noncomputable section

/-! Transfer an all-test composite kernel calculation through a proved
commuting square, before substituting the full native PEL constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem composite_kernel_iff_of_square {S : Scheme} {A B F C T : Over S} [GrpObj C]
    (u : A ⟶ F) (c : F ⟶ B) (f : A ⟶ B) (g : B ⟶ C) (hs : u ≫ c = f)
    (fg : A ⟶ C) (hfg : fg = f ≫ g) (a : T ⟶ A) (P : Prop)
    (hp : a ≫ u ≫ c ≫ g = 1 ↔ P) : a ≫ fg = 1 ↔ P := by
  have he := hfg.trans ((congrArg (fun v => v ≫ g) hs.symm).trans (Category.assoc _ _ _))
  exact (Iff.of_eq (congrArg (fun v => a ≫ v = 1) he)).trans hp

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositeKernelSquare
