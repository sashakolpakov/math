import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Cochain Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CochainEdge.CochainEdgeComparison

noncomputable section

/-! A cochain comparison preserving the original global edge
preserves the corresponding inverse-edge homology comparison. -/

open _root_.CategoryTheory

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L M : CochainComplex A ℕ} (f : K ⟶ L) (e : L ≅ M) (g : K ⟶ M)
  (h : f ≫ e.hom = g) [QuasiIso g] (i : ℕ) {B : A} (k : K.homology i ≅ B)

include h in
theorem homology : HomologicalComplex.homologyMap f i ≫
    ((HomologicalComplex.homologyFunctor A (.up ℕ) i).mapIso e ≪≫
      (asIso (HomologicalComplex.homologyMap g i)).symm ≪≫ k).hom = k.hom := by
  have hc : HomologicalComplex.homologyMap f i ≫ HomologicalComplex.homologyMap e.hom i =
      HomologicalComplex.homologyMap g i :=
    (HomologicalComplex.homologyMap_comp _ _ i).symm.trans
      (congrArg (fun q => HomologicalComplex.homologyMap q i) h)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (asIso (HomologicalComplex.homologyMap g i)).inv ≫ k.hom) hc).trans
      ((asIso (HomologicalComplex.homologyMap g i)).hom_inv_id_assoc _))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CochainEdge.CochainEdgeComparison
