import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.DiagonalConeNaturality

/-! # Diagonal Cone Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalConeChange.SectionDiagonalConeChange

noncomputable section

/-! Canonical section diagonal cones commute with an actual section
restriction and an augmented coefficient-complex diagram map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w v' w' z t
variable (C : Type u) [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Preadditive A]
  {A' : Type v'} [Category.{w'} A'] [Preadditive A']
  {B : Type z} [Category.{t} B] [Preadditive B]
  (T : A ⥤ A') [T.Additive] (S : A ⥤ Cᵒᵖ ⥤ B) [S.Additive]
  (S' : A' ⥤ Cᵒᵖ ⥤ B) [S'.Additive]
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex A' ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : S ⟶ T ⋙ S')

local notation "rowsP" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor S P
local notation "rowsQ" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor.functor S' Q
local notation "rowsMap" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange.SectionComplexBifunctorChange.rows T S S' P Q a b
local notation "complexesMap" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange.SectionComplexBifunctorChange.complexes T S S' P Q a b

def diagonalMap : DiagonalCone.SectionDiagonalCone.source C S P ⟶ DiagonalCone.SectionDiagonalCone.source C S' Q :=
  Semilattice.DiagonalConeNaturality.SemilatticeDiagonalConeNaturality.diagonalMap C rowsP rowsQ rowsMap

theorem assembly_natural : Semilattice.DiagonalConeNaturality.SemilatticeDiagonalConeNaturality.diagramMap C rowsP rowsQ rowsMap ≫
    (ComplexAssembly.SectionComplexAssembly.iso S' Q).hom = (ComplexAssembly.SectionComplexAssembly.iso S P).hom ≫ complexesMap := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext I
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable
  (hP : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hQ : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S' Q).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

theorem cone : DiagonalCone.SectionDiagonalCone.cone C S P hP ≫ complexesMap =
    (Functor.const Cᵒᵖ).map (diagonalMap C T S S' P Q a b) ≫ DiagonalCone.SectionDiagonalCone.cone C S' Q hQ :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => Semilattice.DiagonalCone.SemilatticeDiagonalCone.cone C rowsP hP ≫ q)
      (assembly_natural C T S S' P Q a b).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ (ComplexAssembly.SectionComplexAssembly.iso S' Q).hom)
            (Semilattice.DiagonalConeNaturality.SemilatticeDiagonalConeNaturality.cone C rowsP rowsQ hP hQ rowsMap)).trans
              (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalConeChange.SectionDiagonalConeChange
