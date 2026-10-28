import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.Iso
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedReindex

/-! # Refined Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedIso.CechAssemblyRefinedIso

noncomputable section

/-! The original assembled Cech isomorphism commutes with actual
projected cover refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (q : ℕ) (t : Fin (q + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  {P Q : Dᵒᵖ ⥤ CochainComplex A ℕ} (e : P ≅ Q)

theorem naturality : (Iso.CechAssemblyIso.totalIso (IntegralComparison.NonemptyCechNerve.nerve V) e).hom ≫
    CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) Q) =
      CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.map F U V r (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P) ≫
        (Iso.CechAssemblyIso.totalIso (IntegralComparison.NonemptyCechNerve.nerve U) (Functor.isoWhiskerLeft F.op e)).hom :=
  CechPresheaf.RefinedReindex.CechPresheafRefinedReindex.naturality F U V r (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) e.hom)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.RefinedIso.CechAssemblyRefinedIso
