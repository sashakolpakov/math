import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PoincareClass

/-! # Multiple Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction

noncomputable section

/-!
On geometric fibers, every multiple of the original polarization has a
unique diagonal-normalized symmetry of its actual Poincare line. The
proof uses additivity of the original Poincare family and the original
ample-line formula; symmetry is not supplied as extra input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

def originalPoincareFamilyLine (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (φ : A.scheme ⟶ D.abelian.scheme) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left := D.poincare.pullback (φ ⊗ₘ 𝟙 A.scheme).left

theorem originalPoincareFamilyLine_class {k : Type} [Field k] [IsAlgClosed k]
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (φ : A.scheme ⟶ D.abelian.scheme) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine D φ) =
      PELModuli.IntegralModel.PoincareClass.PoincareClasses.pairClass D (fst A.scheme A.scheme ≫ φ) (snd A.scheme A.scheme) := by
  have h : φ ⊗ₘ 𝟙 A.scheme = lift (fst A.scheme A.scheme ≫ φ) (snd A.scheme A.scheme) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  exact congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))
    (congrArg Over.Hom.left h)

theorem originalPoincareFamilyLine_multiple {k : Type} [Field k] [IsAlgClosed k]
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (φ : A.scheme ⟶ D.abelian.scheme) (n : ℕ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine D (φ ^ n)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine D φ) ^ n := by
  have : IsProper (A.scheme ⊗ A.scheme).hom := by dsimp; infer_instance
  have : CompactSpace (A.scheme ⊗ A.scheme).left :=
    QuasiCompact.compactSpace_of_compactSpace (A.scheme ⊗ A.scheme).hom
  have : QuasiSeparatedSpace (A.scheme ⊗ A.scheme).left :=
    quasiSeparatedSpace_of_quasiSeparated (A.scheme ⊗ A.scheme).hom
  rw [originalPoincareFamilyLine_class, originalPoincareFamilyLine_class, MonObj.comp_pow]
  exact PELModuli.IntegralModel.PoincareClass.PoincareClasses.pairClass_pow_left D _ _ n

theorem originalPoincareFamilyLine_multiple_symmetry {k : Type} [Field k] [IsAlgClosed k]
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (φ : A.scheme ⟶ D.abelian.scheme) (n : ℕ)
    (hsym : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (β_ A.scheme A.scheme).hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine D φ)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine D φ)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (β_ A.scheme A.scheme).hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine D (φ ^ n))) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine D (φ ^ n)) := by
  rw [originalPoincareFamilyLine_multiple]
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (β_ A.scheme A.scheme).hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine D φ) ^ n) = _
  rw [map_pow]
  exact congrArg (fun c => c ^ n) hsym

set_option backward.isDefEq.respectTransparency false in
theorem geometricOriginalPoincareLine_symmetry
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) :
    let B := A.pullback s
    let φ := (Over.pullback s).map pol.isogeny.hom
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (β_ B.scheme B.scheme).hom.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine (D.pullback s) φ)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (originalPoincareFamilyLine (D.pullback s) φ) := by
  obtain ⟨L, _, _, hformula⟩ := PolarizationPoincareComparison.Construction.canonicalPositiveOnGeometricFiber_ofHilbertConstruction A D pol.isogeny.hom k s (pol.positive k s)
  exact PolarizationLineSymmetry.Construction.lineClass_symmetry_of_polarization_formula (A.pullback s).scheme
    (originalPoincareFamilyLine (D.pullback s) ((Over.pullback s).map pol.isogeny.hom)) L hformula

theorem geometricPoincareMultiple_diagonal_symmetry
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) :
    let B := (A.pullback s).scheme
    let P := originalPoincareFamilyLine (D.pullback s) (((Over.pullback s).map pol.isogeny.hom) ^ n)
    ∃! σ : (Scheme.Modules.pullback (β_ B B).hom.left).obj P.sheaf ≅ P.sheaf,
      (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal B).left).mapIso σ = DiagonalLineSymmetry.Construction.diagonalSymmetryComparison B P := by
  let P := originalPoincareFamilyLine (D.pullback s) (((Over.pullback s).map pol.isogeny.hom) ^ n)
  have h := originalPoincareFamilyLine_multiple_symmetry (D.pullback s)
    ((Over.pullback s).map pol.isogeny.hom) n (geometricOriginalPoincareLine_symmetry D pol k s)
  exact DiagonalLineSymmetry.Construction.existsUnique_diagonalLineSymmetry_of_iso (A.pullback s).scheme P
    (Classical.choice (Quotient.exact h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction
