import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi

/-! # Complex Assembly -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexAssembly.SectionComplexAssembly

noncomputable section

/-! Reassembling the section bifunctor recovers the original
presheaf-valued complex functor, with identity degree components. -/

open _root_.CategoryTheory

universe u v w z r s t q
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {A : Type r} [Category.{s} A] [Preadditive A]
  {B : Type t} [Category.{q} B] [Preadditive B]
  (S : A ⥤ D ⥤ B) [S.Additive] (P : C ⥤ CochainComplex A ℕ)

def iso : (ComplexBifunctor.SectionComplexBifunctor.functor S P).flip ⋙ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ) ≅
    P ⋙ S.mapHomologicalComplex (.up ℕ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

theorem hom_app_f (X : C) (I : D) (n : ℕ) : (((iso S P).hom.app X).f n).app I =
    𝟙 ((S.obj ((P.obj X).X n)).obj I) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexAssembly.SectionComplexAssembly
