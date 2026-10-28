import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Bundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

/-! # Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Normalization and the diagonal description of the Poincare graph bundle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {g : ℕ} {S T : Scheme.{u}} {A : Abelian.Schemes.AbelianScheme g S}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)

/-- The relative diagonal of an abelian scheme. -/
def Abelian.Schemes.AbelianScheme.diagonalMap (A : Abelian.Schemes.AbelianScheme g S) :
    A.scheme ⟶ A.scheme ⊗ A.scheme := lift (𝟙 A.scheme) (𝟙 A.scheme)

theorem PoincareGraph.Fibers.poincareGraphMap_zero [IsMonHom p] :
    η[A.scheme] ≫ PoincareGraph.Bundles.poincareGraphMap D p =
      η[A.scheme] ≫ lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme) := by
  simp only [PoincareGraph.Bundles.poincareGraphMap, comp_lift, IsMonHom.one_hom, Category.comp_id]
  congr 1
  simp only [MonObj.comp_one, MonObj.one_eq_one]

/-- A homomorphism to the dual gives a graph bundle normalized at zero. -/
def PoincareGraph.Fibers.poincareGraphBundle_zeroIso [IsMonHom p] :
    (Line.Bundles.LineBundle.pullback η[A.scheme].left (PoincareGraph.Bundles.poincareGraphBundle D p)).sheaf ≅
      Line.Bundles.structureModule S :=
  (Scheme.Modules.pullbackComp η[A.scheme].left (PoincareGraph.Bundles.poincareGraphMap D p).left).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (PoincareGraph.Fibers.poincareGraphMap_zero D p))).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp η[A.scheme].left
      (lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)).left).symm.app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback η[A.scheme].left).mapIso D.normalizedAtDualZero.some ≪≫
    Line.Bundles.structureModulePullbackIso η[A.scheme].left

/-- On each base change, the diagonal of the biextension is the original graph map. -/
theorem PoincareGraph.Fibers.polarizationBiextensionMap_diagonal (f : T ⟶ S) :
    (A.pullback f).diagonalMap.left ≫ Polarization.FiberComparison.polarizationBiextensionMap D p f =
      pullback.fst A.scheme.hom f ≫ (PoincareGraph.Bundles.poincareGraphMap D p).left := by
  let q := (Over.pullback f).map p ⊗ₘ 𝟙 (A.pullback f).scheme
  have diagonal_tensor {X Y : Over T} (a : X ⟶ Y) :
      lift (𝟙 X) (𝟙 X) ≫ (a ⊗ₘ 𝟙 X) = lift a (𝟙 X) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst,
        Category.id_comp]
    · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd,
        Category.id_comp]
  have h : (A.pullback f).diagonalMap ≫ q =
      PoincareGraph.Bundles.poincareGraphMap (D.pullback f) ((Over.pullback f).map p) := by
    exact diagonal_tensor ((Over.pullback f).map p)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg₂ (fun a b => a ≫ b) (congrArg Over.Hom.left h)
      (Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D f)).trans
      (PoincareGraph.Bundles.poincareGraphMap_baseChange D p f))

/-- The diagonal pullback of the fiber biextension is the fiber of the global graph bundle. -/
def PoincareGraph.Fibers.polarizationBiextensionDiagonalIso (f : T ⟶ S) :
    (Line.Bundles.LineBundle.pullback (A.pullback f).diagonalMap.left
      (PolarizationData.polarizationBiextensionAt D p f)).sheaf ≅
      (Line.Bundles.LineBundle.pullback (pullback.fst A.scheme.hom f) (PoincareGraph.Bundles.poincareGraphBundle D p)).sheaf :=
  (Scheme.Modules.pullbackComp (A.pullback f).diagonalMap.left
    (Polarization.FiberComparison.polarizationBiextensionMap D p f)).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (PoincareGraph.Fibers.polarizationBiextensionMap_diagonal D p f)).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp (pullback.fst A.scheme.hom f)
      (PoincareGraph.Bundles.poincareGraphMap D p).left).symm.app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
