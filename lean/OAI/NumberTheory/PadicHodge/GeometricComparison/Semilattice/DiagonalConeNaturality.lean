import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.DiagonalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalApp

/-! # Diagonal Cone Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.DiagonalConeNaturality.SemilatticeDiagonalConeNaturality

noncomputable section

/-! Canonical diagonal cones are natural in maps of bifunctors whose
meet restrictions are invertible. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

section

universe u v w
variable (C : Type u) [SemilatticeInf C] {A : Type v} [Category.{w} A]
  (P Q : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (hP : ∀ I V : C, IsIso ((P.obj (op I)).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hQ : ∀ I V : C, IsIso ((Q.obj (op I)).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (a : P ⟶ Q)

theorem functor_cone : DiagonalCone.SemilatticeDiagonalCone.functorCone C P hP ≫ (flipFunctor _ _ _).map a =
    (Functor.const Cᵒᵖ).map (BifunctorDiagonalApp.BifunctorDiagonalMap.map a) ≫ DiagonalCone.SemilatticeDiagonalCone.functorCone C Q hQ := by
  apply NatTrans.ext
  funext V
  apply NatTrans.ext
  funext I
  have h := LocalCone.SemilatticeLocalCone.factorization C I.unop (Q.obj I) (hQ I.unop)
    ((P.obj I).obj I) (LocalCone.SemilatticeLocalCone.cone C I.unop (P.obj I) (hP I.unop) ≫ a.app I)
  have hs : ((LocalCone.SemilatticeLocalCone.cone C I.unop (P.obj I) (hP I.unop) ≫ a.app I).app I) =
      (a.app I).app I :=
    (congrArg (fun q => q ≫ (a.app I).app I) (LocalCone.SemilatticeLocalCone.self C I.unop (P.obj I) (hP I.unop))).trans
      (Category.id_comp _)
  exact congrArg (fun η => η.app V)
    (h.trans (congrArg (fun q => (Functor.const Cᵒᵖ).map q ≫
      LocalCone.SemilatticeLocalCone.cone C I.unop (Q.obj I) (hQ I.unop)) hs))

end

universe u v w
variable (C : Type u) [SemilatticeInf C] {A : Type v} [Category.{w} A] [HasZeroMorphisms A]
  (P Q : Cᵒᵖ ⥤ Cᵒᵖ ⥤ CochainComplex A ℕ)
  (hP : ∀ I V : C, IsIso ((P.obj (op I)).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hQ : ∀ I V : C, IsIso ((Q.obj (op I)).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (a : P ⟶ Q)

def diagonalMap : DiagonalCone.SemilatticeDiagonalCone.source C P ⟶ DiagonalCone.SemilatticeDiagonalCone.source C Q :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (BifunctorDiagonalApp.BifunctorDiagonalMap.map a)

def diagramMap : DiagonalCone.SemilatticeDiagonalCone.diagram C P ⟶ DiagonalCone.SemilatticeDiagonalCone.diagram C Q :=
  Functor.whiskerRight ((flipFunctor _ _ _).map a) (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ))

theorem cone : DiagonalCone.SemilatticeDiagonalCone.cone C P hP ≫ diagramMap C P Q a =
    (Functor.const Cᵒᵖ).map (diagonalMap C P Q a) ≫ DiagonalCone.SemilatticeDiagonalCone.cone C Q hQ := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext I
  have h := congrArg (fun η => ((η.app V).app I).f i) (functor_cone C P Q hP hQ a)
  change ((LocalCone.SemilatticeLocalCone.cone C I.unop (P.obj I) (hP I.unop)).app V).f i ≫
      ((a.app I).app V).f i = ((a.app I).app I).f i ≫
        ((LocalCone.SemilatticeLocalCone.cone C I.unop (Q.obj I) (hQ I.unop)).app V).f i at h
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f, DiagonalCone.SemilatticeDiagonalCone.cone_app_f]
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.DiagonalConeNaturality.SemilatticeDiagonalConeNaturality
