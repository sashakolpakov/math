import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Fibers

/-! # Graph Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Pulling the polarization formula to the diagonal identifies the global graph bundle on a fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S T : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}

def Abelian.Schemes.AbelianScheme.doubleMap (A : Abelian.Schemes.AbelianScheme g S) : A.scheme ⟶ A.scheme :=
  A.diagonalMap ≫ μ[A.scheme]

theorem Abelian.Schemes.AbelianScheme.doubleMap_eq_square (A : Abelian.Schemes.AbelianScheme g S) :
    A.doubleMap = (𝟙 A.scheme) ^ 2 := by
  simp only [Abelian.Schemes.AbelianScheme.doubleMap, Abelian.Schemes.AbelianScheme.diagonalMap, pow_two, Hom.mul_def]

def Polarization.GraphFormula.diagonalFirstPullbackIso (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left) :
    (Line.Bundles.LineBundle.pullback A.diagonalMap.left
      (Line.Bundles.LineBundle.pullback (fst A.scheme A.scheme).left L)).sheaf ≅ L.sheaf :=
  (Scheme.Modules.pullbackComp A.diagonalMap.left (fst A.scheme A.scheme).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      (lift_fst (𝟙 A.scheme) (𝟙 A.scheme)))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackId A.scheme.left).app L.sheaf

def Polarization.GraphFormula.diagonalSecondPullbackIso (A : Abelian.Schemes.AbelianScheme g S) (L : Line.Bundles.LineBundle A.scheme.left) :
    (Line.Bundles.LineBundle.pullback A.diagonalMap.left
      (Line.Bundles.LineBundle.pullback (snd A.scheme A.scheme).left L)).sheaf ≅ L.sheaf :=
  (Scheme.Modules.pullbackComp A.diagonalMap.left (snd A.scheme A.scheme).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      (lift_snd (𝟙 A.scheme) (𝟙 A.scheme)))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackId A.scheme.left).app L.sheaf

/-- Restricting the biextension formula to the diagonal gives a formula for the graph bundle. -/
def Polarization.GraphFormula.polarizationGraphFormulaIso (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)
    (f : T ⟶ S) (L : Line.Bundles.LineBundle (A.pullback f).scheme.left)
    (e : Tensor.ProductSheaf.tensorModule
      (Tensor.ProductSheaf.tensorModule (PolarizationData.polarizationBiextensionAt D p f).sheaf
        (Line.Bundles.LineBundle.pullback (fst (A.pullback f).scheme (A.pullback f).scheme).left L).sheaf)
      (Line.Bundles.LineBundle.pullback (snd (A.pullback f).scheme (A.pullback f).scheme).left L).sheaf ≅
      (Line.Bundles.LineBundle.pullback μ[(A.pullback f).scheme].left L).sheaf) :
    Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule
      (Line.Bundles.LineBundle.pullback (pullback.fst A.scheme.hom f) (PoincareGraph.Bundles.poincareGraphBundle D p)).sheaf L.sheaf)
      L.sheaf ≅ (Line.Bundles.LineBundle.pullback (A.pullback f).doubleMap.left L).sheaf := by
  let B := A.pullback f
  let E := PolarizationData.polarizationBiextensionAt D p f
  let L₁ := Line.Bundles.LineBundle.pullback (fst B.scheme B.scheme).left L
  let L₂ := Line.Bundles.LineBundle.pullback (snd B.scheme B.scheme).left L
  let d := B.diagonalMap.left
  let c : (Line.Bundles.LineBundle.pullback d ((E.tensor L₁).tensor L₂)).sheaf ≅
      Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule
        (Line.Bundles.LineBundle.pullback (pullback.fst A.scheme.hom f) (PoincareGraph.Bundles.poincareGraphBundle D p)).sheaf L.sheaf)
        L.sheaf :=
    Line.Bundles.LineBundle.tensorBaseChangeIso d (E.tensor L₁) L₂ ≪≫
      Tensor.ProductSheaf.tensorModuleCongr (Line.Bundles.LineBundle.tensorBaseChangeIso d E L₁)
        (Polarization.GraphFormula.diagonalSecondPullbackIso B L) ≪≫
      Tensor.ProductSheaf.tensorModuleCongr
        (Tensor.ProductSheaf.tensorModuleCongr (PoincareGraph.Fibers.polarizationBiextensionDiagonalIso D p f) (Polarization.GraphFormula.diagonalFirstPullbackIso B L))
        (Iso.refl L.sheaf)
  exact c.symm ≪≫ (Scheme.Modules.pullback d).mapIso e ≪≫
    (Scheme.Modules.pullbackComp d μ[B.scheme].left).app L.sheaf

theorem PolarizationData.PositiveOnGeometricFiber.graphFormula {D : Dual.Data.DualAbelianData A}
    {p : A.scheme ⟶ D.abelian.scheme} {K : Type u} [Field K] [IsAlgClosed K]
    {f : Spec (.of K) ⟶ S} (h : PolarizationData.PositiveOnGeometricFiber D p K f) :
    ∃ L : Line.Bundles.LineBundle (A.pullback f).scheme.left, L.IsAmple ∧
      Nonempty ((Line.Bundles.LineBundle.pullback η[(A.pullback f).scheme].left L).sheaf ≅
        Line.Bundles.structureModule (Spec (.of K))) ∧
      Nonempty (Tensor.ProductSheaf.tensorModule (Tensor.ProductSheaf.tensorModule
        (Line.Bundles.LineBundle.pullback (pullback.fst A.scheme.hom f) (PoincareGraph.Bundles.poincareGraphBundle D p)).sheaf L.sheaf)
        L.sheaf ≅ (Line.Bundles.LineBundle.pullback (A.pullback f).doubleMap.left L).sheaf) := by
  obtain ⟨L, hL, h₀, ⟨e⟩⟩ := h
  exact ⟨L, hL, h₀, ⟨Polarization.GraphFormula.polarizationGraphFormulaIso D p f L e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
