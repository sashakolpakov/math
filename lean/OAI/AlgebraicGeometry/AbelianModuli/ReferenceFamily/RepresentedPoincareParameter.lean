import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PicardSmoothCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.PicardInclusionFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass

/-! # Represented Poincare Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPoincareParameter

noncomputable section

/-! The original representing Poincare family separates all parameter
points, and its actual dual group law represents tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {S : Scheme.{u}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A)

theorem representedPoincareParameter_class {T : Over S} (x : T ⟶ D.abelian.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass D.poincare x =
      A.homogeneousPicardSectionInclusion T (D.representable.homEquiv x) := by
  rw [D.pointRelativeClass_eq_poincare]
  unfold RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass
  rw [tensorHom_id]
  rfl

theorem representedPoincareParameter_injective (T : Over S) :
    Function.Injective (fun x : T ⟶ D.abelian.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass D.poincare x) := by
  intro x y h
  apply D.representable.homEquiv.injective
  apply A.homogeneousPicardSectionInclusion_injective T
  exact (representedPoincareParameter_class D x).symm.trans
    (h.trans (representedPoincareParameter_class D y))

theorem representedPoincareParameter_mul {k : Type u} [Field k]
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    {T : Over (Spec (.of k))} (x y : T ⟶ D.abelian.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass D.poincare (x * y) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass D.poincare x * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass D.poincare y := by
  rw [representedPoincareParameter_class, D.homEquiv_mul_overField,
    map_mul, ← representedPoincareParameter_class, ← representedPoincareParameter_class]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentedPoincareParameter
