import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfSheafSectionDescent

/-! # Fppf Sheaf Restriction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfSheafRestriction.Construction

/-! Restriction along a single fppf cover detects equality of sheaf sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u w

theorem fppfSheaf_restriction_injective {S : Scheme.{u}} {X Y : Over S} (q : X ⟶ Y)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type w)) : Function.Injective (F.obj.map q.op) := by
  have hF : Presieve.IsSheaf (Scheme.fppfTopology.over S) F.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  exact Presieve.isSeparatedFor_singleton.mp
    (hF.isSheafFor (Presieve.singleton q) (FormalGeometry.Completion.FppfSheafSectionDescent.Construction.fppfSingleton_cover q)).isSeparatedFor

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfSheafRestriction.Construction
