import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalConeReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone

/-! # Diagonal Cone Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalConeReindex.SectionDiagonalConeReindex

noncomputable section

/-! Canonical section-diagonal cones commute with reindexing both their
open and frame variables, whenever intersection restrictions are invertible. -/

open _root_.CategoryTheory Opposite

universe u v w z r s
variable (C : Type u) [SemilatticeInf C] (D : Type v) [SemilatticeInf D]
  {A : Type w} [Category.{z} A] [Preadditive A]
  {B : Type r} [Category.{s} B] [Preadditive B]
  (F : C ⥤ D) (S : A ⥤ Dᵒᵖ ⥤ B) [S.Additive]
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ)

def precompose : (Dᵒᵖ ⥤ B) ⥤ (Cᵒᵖ ⥤ B) := (Functor.whiskeringLeft _ _ _).obj F.op

instance precompose_additive : (precompose C D (B := B) F).Additive := by
  dsimp only [precompose]
  infer_instance

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalConeReindex.SectionDiagonalConeReindex.precompose C D (B := B) F

def sourceIso : ((H).mapHomologicalComplex (.up ℕ)).obj (DiagonalCone.SectionDiagonalCone.source D S P) ≅
    DiagonalCone.SectionDiagonalCone.source C (S ⋙ H) (F.op ⋙ P) := Iso.refl _

variable
  (hD : ∀ I V : D, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hC : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor (S ⋙ precompose C D (B := B) F)
    (F.op ⋙ P)).obj (op I)).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

theorem cone : Functor.whiskerLeft F.op
    (Functor.whiskerRight (DiagonalCone.SectionDiagonalCone.cone D S P hD) ((H).mapHomologicalComplex (.up ℕ))) =
      DiagonalCone.SectionDiagonalCone.cone C (S ⋙ H) (F.op ⋙ P) hC := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext I
  have h := Semilattice.LocalConeReindex.SemilatticeLocalConeReindex.cone C D F I.unop
    ((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (F.op.obj I)) (hC I.unop) (hD (F.obj I.unop))
  exact (DiagonalCone.SectionDiagonalCone.cone_app_f D S P hD (F.op.obj V) (F.op.obj I) i).trans
    ((congrArg (fun a => (a.app V).f i) h).symm.trans
      (DiagonalCone.SectionDiagonalCone.cone_app_f C (S ⋙ H) (F.op ⋙ P) hC V I i).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalConeReindex.SectionDiagonalConeReindex
