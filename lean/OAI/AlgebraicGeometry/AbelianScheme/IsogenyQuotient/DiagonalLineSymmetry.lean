import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationLineSymmetry
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidificationAt

/-! # Diagonal Line Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction

noncomputable section

/-!
Over a field, the actual polarization line has a unique symmetry whose
restriction to the diagonal is the canonical identity comparison.
Proper connected group schemes have no extra global functions, so
restriction along the diagonal determines line-bundle isomorphisms.
This normalization is derived from the original polarization formula.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

def groupDiagonal {S : Scheme.{u}} (A : Over S) : A ⟶ A ⊗ A := lift (𝟙 A) (𝟙 A)

theorem groupDiagonal_swap {S : Scheme.{u}} (A : Over S) :
    groupDiagonal A ≫ (β_ A A).hom = groupDiagonal A := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [groupDiagonal]

def diagonalSymmetryComparison {S : Scheme.{u}} (A : Over S) (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) :
    (Scheme.Modules.pullback (groupDiagonal A).left).obj
      ((Scheme.Modules.pullback (β_ A A).hom.left).obj P.sheaf) ≅
        (Scheme.Modules.pullback (groupDiagonal A).left).obj P.sheaf :=
  (Scheme.Modules.pullbackComp (groupDiagonal A).left (β_ A A).hom.left).app P.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (groupDiagonal_swap A))).app P.sheaf

theorem groupDiagonal_appTop_isIso
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] :
    IsIso (groupDiagonal A).left.appTop := by
  have : Smooth (A ⊗ A).hom := by dsimp; infer_instance
  have : IsProper (A ⊗ A).hom := by dsimp; infer_instance
  have : GeometricallyConnected (A ⊗ A).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst A.hom A.hom) A.hom
  have : IsIso A.hom.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso A
  have : IsIso (A ⊗ A).hom.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroup_appTop_isIso (A ⊗ A)
  have h : IsIso ((A ⊗ A).hom.appTop ≫ (groupDiagonal A).left.appTop) := by
    rw [← Scheme.Hom.comp_appTop, Over.w]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp h

theorem existsUnique_diagonalLineSymmetry_of_iso
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left)
    (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj P.sheaf ≅ P.sheaf) :
    ∃! τ : (Scheme.Modules.pullback (β_ A A).hom.left).obj P.sheaf ≅ P.sheaf,
      (Scheme.Modules.pullback (groupDiagonal A).left).mapIso τ = diagonalSymmetryComparison A P := by
  have : IsIso (groupDiagonal A).left.appTop := groupDiagonal_appTop_isIso A
  exact Quotients.FiniteDescent.LineRigidificationAt.Construction.LineRigidification.existsUnique_iso (groupDiagonal A).left
    (P.pullback (β_ A A).hom.left) P σ (diagonalSymmetryComparison A P)

theorem existsUnique_diagonalLineSymmetry
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule P.sheaf (L.pullback (fst A A).left).sheaf)
      (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf)) :
    ∃! σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj P.sheaf ≅ P.sheaf,
      (Scheme.Modules.pullback (groupDiagonal A).left).mapIso σ = diagonalSymmetryComparison A P := by
  exact existsUnique_diagonalLineSymmetry_of_iso A P (PolarizationLineSymmetry.Construction.lineSymmetryOfPolarizationFormula A P L hformula)

theorem geometricPolarizationBiextension_diagonal_symmetry
    {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) :
    let B := (A.pullback s).scheme
    let P := AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D pol.isogeny.hom s
    ∃! σ : (Scheme.Modules.pullback (β_ B B).hom.left).obj P.sheaf ≅ P.sheaf,
      (Scheme.Modules.pullback (groupDiagonal B).left).mapIso σ = diagonalSymmetryComparison B P := by
  obtain ⟨L, _, _, hformula⟩ := pol.positive k s
  exact existsUnique_diagonalLineSymmetry (A.pullback s).scheme
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D pol.isogeny.hom s) L hformula

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction
