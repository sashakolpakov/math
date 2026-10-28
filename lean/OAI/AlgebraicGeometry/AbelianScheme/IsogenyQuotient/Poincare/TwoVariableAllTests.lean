import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TwoVariableSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoFourSquares

/-! # Two Variable All Tests -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TwoVariableAllTests.Construction

noncomputable section

section

/-! The full two-variable symmetry expression preserves its actual
five point-fiber comparisons under every map of test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ] (n : ℕ)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (σn : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf)

theorem poincareTwoVariableSymmetryComparison_pullback {T T' : Over (Spec (.of k))}
    (f : T' ⟶ T) (x y : T ⟶ A.scheme) (x' y' : T' ⟶ A.scheme) (hx : f ≫ x = x') (hy : f ≫ y = y')
    (h₀ : f ≫ lift ((y ≫ φ) ^ n) x = lift ((y' ≫ φ) ^ n) x')
    (h₁ : f ≫ lift (y ≫ φ ^ n) x = lift (y' ≫ φ ^ n) x')
    (h₂ : f ≫ lift (x ≫ φ ^ n) y = lift (x' ≫ φ ^ n) y')
    (h₃ : f ≫ lift ((x ^ n) ≫ φ) y = lift ((x' ^ n) ≫ φ) y')
    (h₄ : f ≫ lift (y ≫ φ) (x ^ n) = lift (y' ≫ φ) (x' ^ n)) :
    (Scheme.Modules.pullback f.left).mapIso (TwoVariableSymmetry.Construction.poincareTwoVariableSymmetryComparison D φ n σ σn x y) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ h₄ =
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ h₀ ≪≫
      TwoVariableSymmetry.Construction.poincareTwoVariableSymmetryComparison D φ n σ σn x' y' := by
  have hxn : f ≫ x ^ n = x' ^ n := (MonObj.comp_pow x n f).trans (congrArg (fun a => a ^ n) hx)
  have he₀ := FiberPointTransportNaturality.Construction.fiberPointIso_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _
    (congrArg₂ lift (MonObj.comp_pow φ n y).symm rfl) _ _
    (congrArg₂ lift (MonObj.comp_pow φ n y').symm rfl) h₀ h₁
  have he₁ := SymmetryFibers.Construction.poincareSymmetryFiber_pullback D (φ ^ n) σn f x y x' y' hx hy h₁ h₂
  have he₂ := FiberPointTransportNaturality.Construction.fiberPointIso_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _
    (congrArg₂ lift ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm) rfl) _ _
    (congrArg₂ lift ((MonObj.comp_pow φ n x').trans (MonObj.pow_comp x' n φ).symm) rfl) h₂ h₃
  have he₃ := SymmetryFibers.Construction.poincareSymmetryFiber_pullback D φ σ f y (x ^ n) y' (x' ^ n) hy hxn h₃ h₄
  exact IsoFourSquares.Construction.iso_functor_four_squares (Scheme.Modules.pullback f.left)
    (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _ (congrArg₂ lift (MonObj.comp_pow φ n y).symm rfl))
    (SymmetryFibers.Construction.poincareSymmetryFiber D (φ ^ n) σn x y)
    (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _
      (congrArg₂ lift ((MonObj.comp_pow φ n x).trans (MonObj.pow_comp x n φ).symm) rfl))
    (SymmetryFibers.Construction.poincareSymmetryFiber D φ σ y (x ^ n))
    (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _ (congrArg₂ lift (MonObj.comp_pow φ n y').symm rfl))
    (SymmetryFibers.Construction.poincareSymmetryFiber D (φ ^ n) σn x' y')
    (FiberPointEquality.Construction.fiberPointIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) _ _
      (congrArg₂ lift ((MonObj.comp_pow φ n x').trans (MonObj.pow_comp x' n φ).symm) rfl))
    (SymmetryFibers.Construction.poincareSymmetryFiber D φ σ y' (x' ^ n))
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ h₀)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ h₁)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ h₂)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ h₃)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f _ _ h₄) he₀ he₁ he₂ he₃

end

/-! The full two-variable symmetry formula for the scalar comparison
holds on arbitrary test schemes by restriction from the abelian square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (φ : A.scheme ⟶ D.abelian.scheme) [IsMonHom φ] (n : ℕ)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ).sheaf)
  (σn : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf ≅ (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)).sheaf)
  (hd : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) φ) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))
  (hdn : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σn =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (φ ^ n)) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme))

include hd hdn in
theorem poincareScalarFiberComparison_twoVariable_allTests {T : Over (Spec (.of k))} (x y : T ⟶ A.scheme) :
    ScalarLine.Construction.poincareScalarFiberComparison D n (y ≫ φ) x = TwoVariableSymmetry.Construction.poincareTwoVariableSymmetryComparison D φ n σ σn x y := by
  have : Smooth (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  have : IsProper (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  have : GeometricallyConnected (A.scheme ⊗ A.scheme).hom :=
    GeometricallyConnected.comp (pullback.fst A.scheme.hom A.scheme.hom) A.scheme.hom
  have : CompactSpace (A.scheme ⊗ A.scheme).left :=
    QuasiCompact.compactSpace_of_compactSpace (A.scheme ⊗ A.scheme).hom
  have : QuasiSeparatedSpace (A.scheme ⊗ A.scheme).left :=
    quasiSeparatedSpace_of_quasiSeparated (A.scheme ⊗ A.scheme).hom
  let X := fst A.scheme A.scheme
  let Y := snd A.scheme A.scheme
  have hb : lift x y ≫ lift (Y ≫ φ) X = lift (y ≫ φ) x := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [X, Y, Category.assoc, lift_fst, lift_snd, lift_snd_assoc]
  have h₀ : lift x y ≫ lift ((Y ≫ φ) ^ n) X = lift ((y ≫ φ) ^ n) x := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [X, Y, Category.assoc, lift_fst, lift_snd, MonObj.comp_pow, lift_snd_assoc]
  have h₁ : lift x y ≫ lift (Y ≫ φ ^ n) X = lift (y ≫ φ ^ n) x := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [X, Y, Category.assoc, lift_fst, lift_snd, lift_snd_assoc]
  have h₂ : lift x y ≫ lift (X ≫ φ ^ n) Y = lift (x ≫ φ ^ n) y := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [X, Y, Category.assoc, lift_fst, lift_snd, lift_fst_assoc]
  have h₃ : lift x y ≫ lift ((X ^ n) ≫ φ) Y = lift ((x ^ n) ≫ φ) y := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, MonObj.comp_pow]
      rw [show lift x y ≫ X = x from lift_fst _ _]
    · simp only [Y, Category.assoc, lift_snd]
  have h₄ : lift x y ≫ lift (Y ≫ φ) (X ^ n) = lift (y ≫ φ) (x ^ n) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [X, Y, Category.assoc, lift_fst, lift_snd, MonObj.comp_pow, lift_snd_assoc]
  have he := ScalarNaturality.Construction.poincareScalarFiberComparison_pullback D n (lift x y) (Y ≫ φ) X (y ≫ φ) x hb h₀ h₄
  have hs := poincareTwoVariableSymmetryComparison_pullback D φ n σ σn (lift x y) X Y x y
    (lift_fst _ _) (lift_snd _ _) h₀ h₁ h₂ h₃ h₄
  exact FiberPointTransportNaturality.Construction.iso_transport_eq (Scheme.Modules.pullback (lift x y).left)
    (ScalarLine.Construction.poincareScalarFiberComparison D n (Y ≫ φ) X) (TwoVariableSymmetry.Construction.poincareTwoVariableSymmetryComparison D φ n σ σn X Y)
    (ScalarLine.Construction.poincareScalarFiberComparison D n (y ≫ φ) x) (TwoVariableSymmetry.Construction.poincareTwoVariableSymmetryComparison D φ n σ σn x y)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift x y) _ _ h₀)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) (lift x y) _ _ h₄) he hs
    (TwoVariableSymmetry.Construction.poincareScalarFiberComparison_twoVariableSymmetry D φ n σ σn hd hdn X Y)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TwoVariableAllTests.Construction
