import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionPairing

/-! # Pairing Independence -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Picard.PoincareBundle.Reference.PairingIndependence.ReferenceTorsion

/-! The original Poincare bundle and its inducing line determine the full torsion pairing without auxiliary product or symmetry inputs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : A.scheme ⟶ D.abelian.scheme) [IsMonHom ell] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)) (n : ℕ)

attribute [local instance] Kernel.Scheme.kernelGroup

/-- The actual full group-scheme pairing, constructed from the inducing-line formula alone. -/
def pairing (T : Over (Spec (.of k))) :
    (T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) →*
      (T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) →* Γ(T.left, ⊤)ˣ :=
  TorsionPairing.Poincare.torsionPairing ell (Line.Comparison.Bundle.fromShared D.poincare)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) n
    (Symmetry.ReferencePoincare.symmetry D ell L hformula n) (Symmetry.ReferencePoincare.symmetry_vertical D ell L hformula n)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange D) (Symmetry.ReferencePoincare.symmetry_horizontal D ell L hformula n) T

/-- The constructed pairing respects every change of test scheme, including nonreduced tests. -/
theorem pairing_natural {T T' : Over (Spec (.of k))} (b : T' ⟶ T)
    (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    pairing D ell L hformula n T' (b ≫ x) (b ≫ y) =
      Units.map b.left.appTop.hom (pairing D ell L hformula n T x y) :=
  TorsionPairing.Poincare.torsionPairing_naturality ell (Line.Comparison.Bundle.fromShared D.poincare)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) n
    (Symmetry.ReferencePoincare.symmetry D ell L hformula n) (Symmetry.ReferencePoincare.symmetry_vertical D ell L hformula n)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange D) (Symmetry.ReferencePoincare.symmetry_horizontal D ell L hformula n) b x y

end AlgebraicGeometry.Picard.PoincareBundle.Reference.PairingIndependence.ReferenceTorsion

namespace AlgebraicGeometry.Picard.PoincareBundle.Reference.PairingIndependence

/-! The canonical full torsion pairing is independent of the inducing line chosen to prove source symmetry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare

attribute [local instance] Kernel.Scheme.kernelGroup

/-- Evaluation of the bilinear wrapper retains the original canonical frame ratio. -/
theorem canonical_pairing_apply {S : Scheme} {A B Z : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
    (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
    (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P)
    (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
    (f : A ⟶ B) [IsMonHom f] (hf : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
    (s : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
    (hs : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) s =
      Poincare.TransverseFrames.sourceVertical φ P Dv)
    (hi : Biextension.Compatibility.Interchange P Dh Dv)
    (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) s =
      Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
    (T : Over S) (x y : T ⟶ Kernel.Scheme.kernelObject f) :
    Canonical.KernelPairing.pairing φ P Dh Dv f hf s hs hi hh T x y =
      Canonical.KernelPairing.value φ P Dh Dv f hf s hs x y := rfl

/-- Equal actual line symmetries give equal canonical frame-ratio values. -/
theorem value_congr_symmetry {S : Scheme} {A B Z : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
    (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
    (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P)
    (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
    (f : A ⟶ B) [IsMonHom f] (hf : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
    (s t : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
    (hs : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) s =
      Poincare.TransverseFrames.sourceVertical φ P Dv)
    (ht : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) t =
      Poincare.TransverseFrames.sourceVertical φ P Dv)
    (hst : s = t) {T : Over S} (x y : T ⟶ Kernel.Scheme.kernelObject f) :
    Canonical.KernelPairing.value φ P Dh Dv f hf s hs x y =
      Canonical.KernelPairing.value φ P Dh Dv f hf t ht x y := by
  cases hst
  rfl

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : A.scheme ⟶ D.abelian.scheme) [IsMonHom ell] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hL : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf))
  (hM : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell).sheaf (M.pullback (fst A.scheme A.scheme).left).sheaf)
    (M.pullback (snd A.scheme A.scheme).left).sheaf ≅ (M.pullback μ[A.scheme].left).sheaf)) (n : ℕ)

omit [IsMonHom ell] in
/-- Diagonal normalization removes every choice of source inducing line from the actual symmetry. -/
theorem symmetry_eq : Symmetry.ReferencePoincare.symmetry D ell L hL n = Symmetry.ReferencePoincare.symmetry D ell M hM n := by
  change Classical.choose (Symmetry.ReferencePoincare.existsUnique_symmetry D ell L hL n) =
    Classical.choose (Symmetry.ReferencePoincare.existsUnique_symmetry D ell M hM n)
  exact (Classical.choose_spec (Symmetry.ReferencePoincare.existsUnique_symmetry D ell M hM n)).2 _
    (Classical.choose_spec (Symmetry.ReferencePoincare.existsUnique_symmetry D ell L hL n)).1

/-- The bundled canonical pairing evaluates to the actual frame-ratio value. -/
theorem pairing_apply (T : Over (Spec (.of k))) (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    ReferenceTorsion.pairing D ell L hL n T x y =
      Canonical.KernelPairing.value (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare)
        (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)
        ((𝟙 A.scheme) ^ n) (TorsionPairing.Poincare.torsion_annihilation ell n)
        (Symmetry.ReferencePoincare.symmetry D ell L hL n) (Symmetry.ReferencePoincare.symmetry_vertical D ell L hL n) x y := by
  unfold ReferenceTorsion.pairing TorsionPairing.Poincare.torsionPairing
  exact canonical_pairing_apply (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)
    ((𝟙 A.scheme) ^ n) (TorsionPairing.Poincare.torsion_annihilation ell n)
    (Symmetry.ReferencePoincare.symmetry D ell L hL n) (Symmetry.ReferencePoincare.symmetry_vertical D ell L hL n)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange D) (Symmetry.ReferencePoincare.symmetry_horizontal D ell L hL n) T x y

/-- All scheme-valued pairing values are independent of the line chosen to witness the original formula. -/
theorem pairing_eq (T : Over (Spec (.of k))) (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    ReferenceTorsion.pairing D ell L hL n T x y =
      ReferenceTorsion.pairing D ell M hM n T x y := by
  rw [pairing_apply D ell L hL n T x y, pairing_apply D ell M hM n T x y]
  exact value_congr_symmetry (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)
    ((𝟙 A.scheme) ^ n) (TorsionPairing.Poincare.torsion_annihilation ell n)
    (Symmetry.ReferencePoincare.symmetry D ell L hL n) (Symmetry.ReferencePoincare.symmetry D ell M hM n)
    (Symmetry.ReferencePoincare.symmetry_vertical D ell L hL n) (Symmetry.ReferencePoincare.symmetry_vertical D ell M hM n)
    (symmetry_eq D ell L M hL hM n) x y

end AlgebraicGeometry.Picard.PoincareBundle.Reference.PairingIndependence

end

end OAI
