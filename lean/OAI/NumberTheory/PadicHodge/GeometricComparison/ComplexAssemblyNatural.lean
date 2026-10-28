import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyPresheaves

/-! # Complex Assembly Natural -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyNatural.ComplexAssemblyCoefficientNaturality

noncomputable section

/-! The original coefficient/complex-assembly isomorphism is natural
in the diagram of complexes. -/

open _root_.CategoryTheory

universe u v a b d e
variable {T : Type u} [Category.{v} T]
  {A : Type a} [Category.{b} A] [Preadditive A]
  {B : Type d} [Category.{e} B] [Preadditive B]
  (F : A ⥤ B) [F.Additive] {P Q : T ⥤ CochainComplex A ℕ} (a : P ⟶ Q)

theorem natural : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℕ))) ≫
    (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F Q).hom =
    (ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.iso F P).hom ≫
      ((ComplexAssemblyPresheaves.ComplexAssemblyCoefficients.presheaves F).mapHomologicalComplex (.up ℕ)).map
        (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) a) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyNatural.ComplexAssemblyCoefficientNaturality
