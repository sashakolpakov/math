import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechRefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.IsoMiddleCancellation

/-! # Diagonal Cech Reference Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechReferenceRefinement.SectionDiagonalCechReferenceRefinement

noncomputable section

/-! The chosen-resolution coordinate isomorphism cancels during
refinement of the original diagonal-to-Cech map. Component formulas
permit native instantiation without normalizing entire complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable (C D : Type) [SemilatticeInf C] [SemilatticeInf D]
  {A : Type u} [Category.{v} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (R : Type 1) [CommRing R] (F : C ⥤ D)
  (S : A ⥤ Dᵒᵖ ⥤ ModuleCat.{2} R) [S.Additive]
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ)
  (hD : ∀ I V : D, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hC : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor
    (S ⋙ DiagonalCechRefinedReindex.SectionDiagonalCechRefinedReindex.pullback C D R F) (F.op ⋙ P)).obj (op I)).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  {M : CochainComplex A ℕ} (e : M ≅ CechCone.Total.CechConeTotal.total V P)

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechRefinedReindex.SectionDiagonalCechRefinedReindex.pullback C D R F

def oldMap : DiagonalCone.SectionDiagonalCone.source D S P ⟶ ((S).mapHomologicalComplex (.up ℕ)).obj M :=
  DiagonalCech.SectionDiagonalCechComparison.map.{0, u, v, 1, 2} D R S P hD V ≫
    ((S).mapHomologicalComplex (.up ℕ)).map e.inv

def refinement : M ⟶ CechCone.Total.CechConeTotal.total U (F.op ⋙ P) :=
  e.hom ≫ CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.map F U V r P

theorem natural : ((H).mapHomologicalComplex (.up ℕ)).map (oldMap D R S P hD V e) ≫
    ((S ⋙ H).mapHomologicalComplex (.up ℕ)).map (refinement C D F P U V r e) =
      DiagonalCech.SectionDiagonalCechComparison.map.{0, u, v, 1, 2} C R (S ⋙ H) (F.op ⋙ P) hC U :=
  (Functor.IsoMiddleCancellation.FunctorIsoMiddleCancellation.square ((S).mapHomologicalComplex (.up ℕ))
    ((H).mapHomologicalComplex (.up ℕ))
    (DiagonalCech.SectionDiagonalCechComparison.map.{0, u, v, 1, 2} D R S P hD V) e
    (CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex.map F U V r P)).trans
      (DiagonalCechRefinedReindex.SectionDiagonalCechRefinedReindex.natural C D R F S P hD hC U V r)

theorem component (q : ℕ) (I : Cᵒᵖ) :
    ((((H).mapHomologicalComplex (.up ℕ)).map (oldMap D R S P hD V e)).f q).app I ≫
      ((((S ⋙ H).mapHomologicalComplex (.up ℕ)).map (refinement C D F P U V r e)).f q).app I =
    ((DiagonalCech.SectionDiagonalCechComparison.map.{0, u, v, 1, 2} C R (S ⋙ H) (F.op ⋙ P) hC U).f q).app I :=
  congrArg (fun a => (a.f q).app I) (natural C D R F S P hD hC U V r e)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechReferenceRefinement.SectionDiagonalCechReferenceRefinement
