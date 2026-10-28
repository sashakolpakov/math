import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.RefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalConeReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCech

/-! # Diagonal Cech Refined Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechRefinedReindex.SectionDiagonalCechRefinedReindex

noncomputable section

/-! In the native coefficient universe, projected cover refinement
identifies the reindexed original diagonal-to-Cech comparison with the
canonical comparison of the reindexed section diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable (C D : Type) [SemilatticeInf C] [SemilatticeInf D]
  {A : Type u} [Category.{v} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (R : Type 1) [CommRing R] (F : C ⥤ D)
  (S : A ⥤ Dᵒᵖ ⥤ ModuleCat.{2} R) [S.Additive]
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ)

def pullback : (Dᵒᵖ ⥤ ModuleCat.{2} R) ⥤ (Cᵒᵖ ⥤ ModuleCat.{2} R) :=
  DiagonalConeReindex.SectionDiagonalConeReindex.precompose C D F

instance pullback_additive : (pullback C D R F).Additive := by
  dsimp only [pullback]
  infer_instance

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechRefinedReindex.SectionDiagonalCechRefinedReindex.pullback C D R F
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.source D S P

variable
  (hD : ∀ I V : D, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hC : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor (S ⋙ pullback C D R F)
    (F.op ⋙ P)).obj (op I)).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

local notation "η" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCone.SectionDiagonalCone.cone D S P hD

omit [HasProducts.{0} A] [HasCoproducts.{0} A] in
theorem mapped_cone : CechCone.RefinedReindex.CechConeComparisonRefinedReindex.mappedCone F S H P M η =
    DiagonalCone.SectionDiagonalCone.cone C (S ⋙ H) (F.op ⋙ P) hC := by
  have h : CechCone.RefinedReindex.CechConeComparisonRefinedReindex.mappedCone F S H P M η =
      Functor.whiskerLeft F.op (Functor.whiskerRight η ((H).mapHomologicalComplex (.up ℕ))) := by
    apply NatTrans.ext
    funext V
    exact CechCone.TotalCoefficientAugmentation.CechConeTotalCoefficientAugmentation.mappedCone_app H (CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped S P) M η (F.op.obj V)
  exact h.trans (DiagonalConeReindex.SectionDiagonalConeReindex.cone C D F S P hD hC)

variable {ι κ : Type} [Finite ι] [Finite κ] (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)

omit [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F] in
theorem refined_eq : CechCone.RefinedReindex.CechConeComparisonRefinedReindex.refined F S H U P M η =
    DiagonalCech.SectionDiagonalCechComparison.map.{0, u, v, 1, 2} C R (S ⋙ H) (F.op ⋙ P) hC U :=
  congrArg (fun θ => CechCone.Total.CechConeTotal.augmentation U (F.op ⋙ CechCone.TotalCoefficient.CechConeTotalCoefficient.mapped (S ⋙ H) P)
    (((H).mapHomologicalComplex (.up ℕ)).obj M) θ ≫
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (S ⋙ H) U (F.op ⋙ P)).inv) (mapped_cone C D R F S P hD hC)

theorem natural : ((H).mapHomologicalComplex (.up ℕ)).map
    (DiagonalCech.SectionDiagonalCechComparison.map.{0, u, v, 1, 2} D R S P hD V) ≫
      ((S ⋙ H).mapHomologicalComplex (.up ℕ)).map (CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.map F U V r P) =
    DiagonalCech.SectionDiagonalCechComparison.map.{0, u, v, 1, 2} C R (S ⋙ H) (F.op ⋙ P) hC U :=
  (CechCone.RefinedReindex.CechConeComparisonRefinedReindex.natural F S H U V r P M η).trans
    (refined_eq C D R F S P hD hC U)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechRefinedReindex.SectionDiagonalCechRefinedReindex
