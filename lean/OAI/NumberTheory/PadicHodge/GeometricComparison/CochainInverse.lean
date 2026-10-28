import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainEdge

/-! # Cochain Inverse -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainInverse.CochainInverseEdgeHomology

noncomputable section

/-! The inverse of the original comparison carries its global
edge to the corresponding original inverse-edge homology map. -/

open _root_.CategoryTheory

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L M : CochainComplex A ℕ} (g : K ⟶ M) (e : L ≅ M) [QuasiIso g]

omit [QuasiIso g] in
theorem square : (g ≫ e.inv) ≫ e.hom = g :=
  (Category.assoc _ _ _).trans ((congrArg (fun x => g ≫ x) e.inv_hom_id).trans (Category.comp_id _))

theorem quasiIso : QuasiIso (g ≫ e.inv) := inferInstance

theorem homology (i : ℕ) {B : A} (k : K.homology i ≅ B) :
    HomologicalComplex.homologyMap (g ≫ e.inv) i ≫
      ((HomologicalComplex.homologyFunctor A (.up ℕ) i).mapIso e ≪≫
        (asIso (HomologicalComplex.homologyMap g i)).symm ≪≫ k).hom = k.hom :=
  CochainEdge.CochainEdgeComparison.homology (g ≫ e.inv) e g (square g e) i k

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainInverse.CochainInverseEdgeHomology
