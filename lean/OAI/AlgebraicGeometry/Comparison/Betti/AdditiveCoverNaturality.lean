import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechCoverCongr

/-! # Additive Cover Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCoverNaturality.Cech

noncomputable section

/-! Equality of covers commutes with the actual maps of coefficient presheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem additiveCechCoverCongrIso_naturality {X : Type} [TopologicalSpace X] {ι : Type}
    {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (f : F ⟶ G) {U V : ι → Opens X} (h : U = V) :
    (cechComplexFunctor U).map f ≫ (AdditiveCechCoverCongr.additiveCechCoverCongrIso G h).hom =
      (AdditiveCechCoverCongr.additiveCechCoverCongrIso F h).hom ≫ (cechComplexFunctor V).map f := by
  subst V
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCoverNaturality.Cech
