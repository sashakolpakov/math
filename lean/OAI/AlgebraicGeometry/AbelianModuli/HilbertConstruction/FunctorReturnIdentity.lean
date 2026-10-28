import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpecIsoProjections

/-! # Functor Return Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FunctorReturnIdentity

noncomputable section

/-! Convert a functorial return isomorphism to its explicit inverse maps. -/
open _root_.CategoryTheory
theorem functorReturnIdentity {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) (k : F.obj Y ≅ F.obj X)
    (h : (F.mapIso e.symm ≪≫ k.symm).hom = 𝟙 (F.obj Y)) :
    F.map e.inv ≫ k.inv = 𝟙 (F.obj Y) := h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FunctorReturnIdentity
