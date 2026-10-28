import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add

/-! # Class Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ClassCoefficientNaturality

noncomputable section

/-! A specified equality of literal coefficient cochains identifies
their native sheaf classes through the original coefficient map. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem cechSheafClass_eq_map_of_coefficient {X : TopCat.{0}} {I : Type}
    (U : I → Opens X) {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (hU : iSup U = ⊤) (n : ℕ) (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (l : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain G.obj U (n + 1))
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0)
    (hl : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta G.obj U (n + 1) l = 0)
    (he : l = DivisorClass.Chern.Abelian.CechClasses.abelianCechCoefficient U f.hom (n + 1) k) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U G hU n l hl =
      CategoryTheory.Sheaf.H.map f (n + 1) (DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n k hk) := by
  subst l
  exact (DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass_naturality U f hU n k hk).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ClassCoefficientNaturality
