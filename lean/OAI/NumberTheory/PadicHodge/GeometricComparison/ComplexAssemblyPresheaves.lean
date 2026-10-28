import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Complex Assembly Presheaves -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients

noncomputable section

/-! Coefficient change commutes with assembling the original complex-valued diagram. -/

open _root_.CategoryTheory

universe u v a b d e
variable {T : Type u} [Category.{v} T]
  {A : Type a} [Category.{b} A] [Preadditive A]
  {B : Type d} [Category.{e} B] [Preadditive B]
  (F : A ⥤ B) [F.Additive] (P : T ⥤ CochainComplex A ℕ)

def presheaves : (T ⥤ A) ⥤ (T ⥤ B) := (Functor.whiskeringRight T A B).obj F

instance presheaves_additive : (presheaves (T := T) F).Additive := by
  dsimp only [presheaves]
  infer_instance

def iso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (P ⋙ F.mapHomologicalComplex (.up ℕ)) ≅
    ((presheaves F).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) P) :=
  (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyTrans.ComplexAssemblyTransport.iso (𝟭 T) F (.up ℕ) P).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexAssemblyPresheaves.ComplexAssemblyCoefficients
