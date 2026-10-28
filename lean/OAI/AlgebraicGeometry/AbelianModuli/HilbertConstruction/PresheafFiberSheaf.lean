import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Presheaf Fiber Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafFiberSheaf

noncomputable section

/-! Prescribing the value of a morphism of sheaves gives a sheaf of normalized sections. -/

open _root_.CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] {P Q : Cᵒᵖ ⥤ Type w}

def presheafSectionFiber (α : P ⟶ Q) (b : Q.sections) : Subfunctor P where
  obj U := {s | α.app U s = b.val U}
  map {U V} f := by
    intro s hs
    change α.app U s = b.val U at hs
    change α.app V (P.map f s) = b.val V
    exact (α.naturality_apply f s).trans ((congrArg (Q.map f) hs).trans (b.property f))

theorem presheafSectionFiber_isSheaf (J : GrothendieckTopology C) (α : P ⟶ Q) (b : Q.sections)
    (hP : Presheaf.IsSheaf J P) (hQ : Presheaf.IsSheaf J Q) :
    Presheaf.IsSheaf J (presheafSectionFiber α b).toFunctor := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  apply ((presheafSectionFiber α b).isSheaf_iff (J := J) ((isSheaf_iff_isSheaf_of_type _ _).mp hP)).mpr
  intro U s hs
  change α.app U s = b.val U
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp hQ) _ hs).isSeparatedFor.ext
  intro V f hf
  have hf' : α.app (.op V) (P.map f.op s) = b.val (.op V) := hf
  exact (α.naturality_apply f.op s).symm.trans (hf'.trans (b.property f.op).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafFiberSheaf
