import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.DiagonalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexAssembly

/-! # Diagonal Cone -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone.SectionDiagonalCone

noncomputable section

/-! The diagonal section complex maps naturally to every original
frame-section complex, and its component on its own chart is invertible. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z t
variable (C : Type u) [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Preadditive A]
  {B : Type z} [Category.{t} B] [Preadditive B]
  (S : A ⥤ Cᵒᵖ ⥤ B) [S.Additive] (P : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (h : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

def source : CochainComplex (Cᵒᵖ ⥤ B) ℕ :=
  Semilattice.DiagonalCone.SemilatticeDiagonalCone.source C (ComplexBifunctor.SectionComplexBifunctor.functor S P)

def cone : (Functor.const Cᵒᵖ).obj (source C S P) ⟶ P ⋙ S.mapHomologicalComplex (.up ℕ) :=
  Semilattice.DiagonalCone.SemilatticeDiagonalCone.cone C (ComplexBifunctor.SectionComplexBifunctor.functor S P) h ≫
    (ComplexAssembly.SectionComplexAssembly.iso S P).hom

theorem cone_app_f (V I : Cᵒᵖ) (n : ℕ) : (((cone C S P h).app V).f n).app I =
    ((Semilattice.LocalCone.SemilatticeLocalCone.cone C I.unop
      ((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj I) (h I.unop)).app V).f n := by
  change (((Semilattice.DiagonalCone.SemilatticeDiagonalCone.cone C (ComplexBifunctor.SectionComplexBifunctor.functor S P) h).app V).f n).app I ≫ 𝟙 _ = _
  exact (Category.comp_id _).trans
    (Semilattice.DiagonalCone.SemilatticeDiagonalCone.cone_app_f C (ComplexBifunctor.SectionComplexBifunctor.functor S P) h V I n)

def evaluationSelfIso (I : C) :
    (((evaluation Cᵒᵖ B).obj (op I)).mapHomologicalComplex (.up ℕ)).obj (source C S P) ≅
      (((evaluation Cᵒᵖ B).obj (op I)).mapHomologicalComplex (.up ℕ)).obj
        ((S.mapHomologicalComplex (.up ℕ)).obj (P.obj (op I))) := Iso.refl _

theorem evaluated_self (I : C) :
    (((evaluation Cᵒᵖ B).obj (op I)).mapHomologicalComplex (.up ℕ)).map ((cone C S P h).app (op I)) =
      (evaluationSelfIso C S P I).hom := by
  ext n : 1
  exact (cone_app_f C S P h (op I) (op I) n).trans
    (congrArg (fun a => a.f n)
      (Semilattice.LocalCone.SemilatticeLocalCone.self C I ((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (op I)) (h I)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone.SectionDiagonalCone
