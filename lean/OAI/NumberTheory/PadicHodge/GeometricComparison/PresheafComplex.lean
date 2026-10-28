import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Presheaf Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafComplex.PresheafComplexExt

/-! Pointwise equality of presheaf-complex maps assembles through
one generic extensionality theorem. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D] [Preadditive D]
  {K L : CochainComplex (C ⥤ D) ℕ} (f g : K ⟶ L)
  (h : ∀ q X, (f.f q).app X = (g.f q).app X)

include h in
theorem ext : f = g :=
  HomologicalComplex.hom_ext f g (fun q => NatTrans.ext (funext (h q)))

end OAI.NumberTheory.PadicHodge.GeometricComparison.PresheafComplex.PresheafComplexExt
