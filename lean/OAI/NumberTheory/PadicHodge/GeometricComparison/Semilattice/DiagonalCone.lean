import OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalEq
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi

/-! # Diagonal Cone -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.DiagonalCone.SemilatticeDiagonalCone

noncomputable section

/-! Canonical row cones assemble into one cone in the category of
presheaf complexes. This keeps all chart restrictions in the global map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

section

universe u v w
variable (C : Type u) [SemilatticeInf C] {A : Type v} [Category.{w} A]
  (P : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (h : ∀ I V : C, IsIso ((P.obj (op I)).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

def component (V : Cᵒᵖ) : BifunctorDiagonalEq.BifunctorDiagonal.functor P ⟶ P.flip.obj V where
  app I := (LocalCone.SemilatticeLocalCone.cone C I.unop (P.obj I) (h I.unop)).app V
  naturality I J f := by
    let hJI : J.unop ≤ I.unop := leOfHom f.unop
    have hf : (homOfLE hJI).op = f := Subsingleton.elim _ _
    have ht := congrArg (fun η => η.app V)
      (LocalConeNaturality.SemilatticeLocalConeNaturality.transition C I.unop (P.obj I) (h I.unop)
        J.unop hJI (P.obj J) (h J.unop) (P.map f))
    rw [NatTrans.comp_app, NatTrans.comp_app, hf] at ht
    rw [BifunctorDiagonalEq.BifunctorDiagonal.map_eq]
    exact ht.symm

def functorCone : (Functor.const Cᵒᵖ).obj (BifunctorDiagonalEq.BifunctorDiagonal.functor P) ⟶ P.flip where
  app := component C P h
  naturality V W f := by
    apply NatTrans.ext
    funext I
    exact (LocalCone.SemilatticeLocalCone.cone C I.unop (P.obj I) (h I.unop)).naturality f

end

universe u v w
variable (C : Type u) [SemilatticeInf C] {A : Type v} [Category.{w} A] [HasZeroMorphisms A]
  (P : Cᵒᵖ ⥤ Cᵒᵖ ⥤ CochainComplex A ℕ)
  (h : ∀ I V : C, IsIso ((P.obj (op I)).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

def source : CochainComplex (Cᵒᵖ ⥤ A) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (BifunctorDiagonalEq.BifunctorDiagonal.functor P)

def diagram : Cᵒᵖ ⥤ CochainComplex (Cᵒᵖ ⥤ A) ℕ :=
  P.flip ⋙ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)

def cone : (Functor.const Cᵒᵖ).obj (source C P) ⟶ diagram C P :=
  (Functor.constComp Cᵒᵖ (BifunctorDiagonalEq.BifunctorDiagonal.functor P) (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ))).inv ≫
    Functor.whiskerRight (functorCone C P h) (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ))

theorem cone_app_f (V I : Cᵒᵖ) (n : ℕ) : (((cone C P h).app V).f n).app I =
    ((LocalCone.SemilatticeLocalCone.cone C I.unop (P.obj I) (h I.unop)).app V).f n := by
  change ((𝟙 _ ≫ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (component C P h V)).f n).app I = _
  rw [Category.id_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.DiagonalCone.SemilatticeDiagonalCone
