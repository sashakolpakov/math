import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarDiagonalSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointTransportNaturality

/-! # Scalar Symmetry All Tests -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarSymmetryAllTests.Construction

noncomputable section

section

/-! The diagonal symmetry expression for the Poincare scalar comparison
retains the actual pullback comparisons on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (n : ℕ)

theorem poincareSymmetryScalarComparison_pullback {T T' : Over (Spec (.of k))}
    (f : T' ⟶ T) (a : T ⟶ A.scheme) (a' : T' ⟶ A.scheme) (ha : f ≫ a = a')
    (hl : f ≫ lift ((a ≫ φ) ^ n) a = lift ((a' ≫ φ) ^ n) a')
    (hm : f ≫ lift ((a ^ n) ≫ φ) a = lift ((a' ^ n) ≫ φ) a')
    (hr : f ≫ lift (a ≫ φ) (a ^ n) = lift (a' ≫ φ) (a' ^ n)) :
    (Scheme.Modules.pullback f.left).mapIso (ScalarDiagonalSymmetry.Construction.poincareSymmetryScalarComparison D φ σ n a) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f (lift (a ≫ φ) (a ^ n)) (lift (a' ≫ φ) (a' ^ n)) hr =
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f (lift ((a ≫ φ) ^ n) a) (lift ((a' ≫ φ) ^ n) a') hl ≪≫
      ScalarDiagonalSymmetry.Construction.poincareSymmetryScalarComparison D φ σ n a' := by
  have ha' : f ≫ a ^ n = a' ^ n := (MonObj.comp_pow a n f).trans (congrArg (fun b => b ^ n) ha)
  have he := FiberPointTransportNaturality.Construction.fiberPointIso_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f
    (lift ((a ≫ φ) ^ n) a) (lift ((a ^ n) ≫ φ) a) (congrArg₂ lift (MonObj.pow_comp a n φ).symm rfl)
    (lift ((a' ≫ φ) ^ n) a') (lift ((a' ^ n) ≫ φ) a') (congrArg₂ lift (MonObj.pow_comp a' n φ).symm rfl) hl hm
  have hd := SymmetryFibers.Construction.poincareSymmetryFiber_pullback D φ σ f a (a ^ n) a' (a' ^ n) ha ha' hm hr
  exact FiberPointTransportNaturality.Construction.iso_functor_square_comp (Scheme.Modules.pullback f.left)
    (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _ (congrArg₂ lift (MonObj.pow_comp a n φ).symm rfl))
    (SymmetryFibers.Construction.poincareSymmetryFiber D φ σ a (a ^ n))
    (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _ (congrArg₂ lift (MonObj.pow_comp a' n φ).symm rfl))
    (SymmetryFibers.Construction.poincareSymmetryFiber D φ σ a' (a' ^ n))
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ hl)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ hm)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ hr) he hd

end

/-! Pulling the normalized identity from the abelian scheme proves
the scalar–symmetry comparison on every test scheme, with no smoothness
or reducedness condition on that test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ]
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (n : ℕ)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))

include hd in
theorem poincareScalarFiberComparison_symmetry_allTests {T : Over (Spec (.of k))} (a : T ⟶ A.scheme) :
    ScalarLine.Construction.poincareScalarFiberComparison D n (a ≫ φ) a = ScalarDiagonalSymmetry.Construction.poincareSymmetryScalarComparison D φ σ n a := by
  have : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  have : QuasiSeparatedSpace A.scheme.left := quasiSeparatedSpace_of_quasiSeparated A.scheme.hom
  have hb : a ≫ lift ((𝟙 A.scheme) ≫ φ) (𝟙 A.scheme) = lift (a ≫ φ) a := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd, Category.id_comp, Category.comp_id]
  have hl : a ≫ lift (((𝟙 A.scheme) ≫ φ) ^ n) (𝟙 A.scheme) = lift ((a ≫ φ) ^ n) a := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have hm : a ≫ lift (((𝟙 A.scheme) ^ n) ≫ φ) (𝟙 A.scheme) = lift ((a ^ n) ≫ φ) a := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, MonObj.comp_pow, Category.comp_id]
    · simp only [Category.assoc, lift_snd, Category.comp_id]
  have hr : a ≫ lift ((𝟙 A.scheme) ≫ φ) ((𝟙 A.scheme) ^ n) = lift (a ≫ φ) (a ^ n) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have he := ScalarNaturality.Construction.poincareScalarFiberComparison_pullback D n a ((𝟙 A.scheme) ≫ φ) (𝟙 A.scheme)
    (a ≫ φ) a hb hl hr
  have hs := poincareSymmetryScalarComparison_pullback D φ σ n a (𝟙 A.scheme) a (Category.comp_id a) hl hm hr
  exact FiberPointTransportNaturality.Construction.iso_transport_eq (Scheme.Modules.pullback a.left)
    (ScalarLine.Construction.poincareScalarFiberComparison D n ((𝟙 A.scheme) ≫ φ) (𝟙 A.scheme))
    (ScalarDiagonalSymmetry.Construction.poincareSymmetryScalarComparison D φ σ n (𝟙 A.scheme))
    (ScalarLine.Construction.poincareScalarFiberComparison D n (a ≫ φ) a) (ScalarDiagonalSymmetry.Construction.poincareSymmetryScalarComparison D φ σ n a)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a _ _ hl)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) a _ _ hr) he hs
    (ScalarDiagonalSymmetry.Construction.poincareScalarFiberComparison_diagonalSymmetry D φ σ n hd (𝟙 A.scheme))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarSymmetryAllTests.Construction
