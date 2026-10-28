import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricGraphDescentCancellation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineTranslation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.KernelLineTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricKernelAmpleDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AmpleLineBundles

/-! # Symmetric Ample Graph Positivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricAmpleGraphPositivity

noncomputable section

/-! An ample symmetric graph line gives an actual ample inducing line.
The construction descends its tensor square along multiplication by two. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
open OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup
  Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

theorem exists_ample_graphTensorSquare_descent
    {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x)
    (h2 : (2 : K) ≠ 0) (hQ : (PoincareGraph.Bundles.poincareGraphBundle D p).IsAmple) :
    ∃ M : Line.Bundles.LineBundle A.scheme.left,
      M.IsAmple ∧
      Nonempty ((M.pullback η[A.scheme].left).sheaf ≅ Line.Bundles.structureModule (Spec (.of K))) ∧
      Nonempty ((M.pullback (A.multiplication 2).left).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle D p).tensor (PoincareGraph.Bundles.poincareGraphBundle D p)).sheaf) := by
  let : GeometricallyIntegral A.scheme.hom :=
    Picard.PoincareBundle.AbelianGeometricIntegrality.geometricallyIntegral A
  let : IsIntegral A.scheme.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton A.scheme.hom
  let : IsLocallyNoetherian A.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  let f : A.scheme ⟶ A.scheme := A.multiplication 2
  let : IsMonHom f := FormalGeometry.Completion.Multiplication.Construction.multiplication_isMonHom A.scheme 2
  let : IsFinite f.left := FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite A.scheme 2 h2
  let : Etale f.left := FormalGeometry.Completion.Multiplication.Construction.multiplication_etale A.scheme 2 h2
  let : Surjective f.left := FormalGeometry.Completion.Multiplication.Construction.multiplication_surjective A.scheme 2 h2
  let H := Picard.PoincareBundle.Kernel.Scheme.kernelObject f
  let i : H ⟶ A.scheme := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f
  let : IsFinite H.hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite f
  have hi2 : i ^ 2 = 1 := by
    calc
      i ^ 2 = i ≫ f := (A.comp_multiplication 2 i).symm
      _ = 1 := Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp f
  have hi : i ≫ (p ^ 2) = 1 := by
    calc
      i ≫ (p ^ 2) = (i ≫ p) ^ 2 := MonObj.comp_pow p 2 i
      _ = (i ^ 2) ≫ p := (MonObj.pow_comp i 2 p).symm
      _ = 1 := by rw [hi2, MonObj.one_comp]
  let Q := PoincareGraph.Bundles.poincareGraphBundle D p
  let L := Picard.PoincareBundle.Line.Comparison.Bundle.fromShared Q
  let P := Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare
  obtain ⟨eQ⟩ := SymmetricGraphInducingFormula.poincareGraph_inducingFormula_double D p hs
  have ef : Tensor.ProductSheaf.tensorModule
      (Tensor.ProductSheaf.tensorModule (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (p ^ 2)).sheaf
        (Q.pullback (fst A.scheme A.scheme).left).sheaf)
      (Q.pullback (snd A.scheme A.scheme).left).sheaf ≅
        (Q.pullback μ[A.scheme].left).sheaf := by
    change Tensor.ProductSheaf.tensorModule
      (Tensor.ProductSheaf.tensorModule (D.poincare.pullback ((p ^ 2) ⊗ₘ 𝟙 A.scheme).left).sheaf
        (Q.pullback (fst A.scheme A.scheme).left).sheaf)
      (Q.pullback (snd A.scheme A.scheme).left).sheaf ≅
        (Q.pullback μ[A.scheme].left).sheaf
    rw [tensorHom_id]
    exact eQ
  obtain ⟨s⟩ := Picard.PoincareBundle.Finite.GroupLineFrame.exists_frame K H
    (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (Q.pullback i.left))
  let t : Picard.PoincareBundle.Line.Fibers.fiber L (snd H A.scheme) ≅ Picard.PoincareBundle.Line.Fibers.fiber L (Picard.PoincareBundle.NormalizedKernelTranslation.action i) :=
    Picard.PoincareBundle.Kernel.LineTransport.translationIso i (p ^ 2) hi P
      D.normalizedAtDualZero.some Q ef s.symm
  let t₂ := Tensor.LineTranslation.PoincareBundle.tensorTranslation i L
    (Picard.PoincareBundle.NormalizedTranslationUnit.translation i L t)
  have hSep : IsSeparated
      (A.scheme.hom ≫ Limits.terminal.from (Spec (.of K))) := inferInstance
  let : IsSeparated (Limits.terminal.from A.scheme.left) :=
    (Limits.terminal.comp_from A.scheme.hom) ▸ hSep
  have hL₂ : (Picard.PoincareBundle.Line.Comparison.Bundle.toShared (Picard.PoincareBundle.Tensor.LineBundles.tensor L L)).IsAmple := by
    change (Q.tensor Q).IsAmple
    exact hQ.tensor hQ
  have ht₂ : ∀ (T : Over (Spec (.of K))) (a b : T ⟶ H),
      Picard.PoincareBundle.Subgroup.DefectParameters.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) t₂ a b =
        Picard.PoincareBundle.Subgroup.DefectParameters.value i (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) t₂ b a := by
    intro T a b
    have ha : a * a = 1 := by
      apply (cancel_mono i).mp
      rw [MonObj.mul_comp, MonObj.one_comp]
      calc
        (a ≫ i) * (a ≫ i) = (a ≫ i) ^ 2 := (pow_two _).symm
        _ = a ≫ (i ^ 2) := (MonObj.comp_pow i 2 a).symm
        _ = 1 := by rw [hi2, MonObj.comp_one]
    exact Tensor.LineTranslation.PoincareBundle.normalized_tensorTranslation_symmetric i L t a b ha
  obtain ⟨M, hM, eM, oM⟩ :=
    AbelianScheme.IsogenyQuotient.SymmetricKernelAmpleDescent.Construction.exists_ample_line_of_symmetric_kernel_transport f
      (Picard.PoincareBundle.Tensor.LineBundles.tensor L L) hL₂ t₂ ht₂
  exact ⟨M, hM, oM, eM⟩

theorem positiveFormula_of_symmetric_ample_graph
    {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
    (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x)
    (h2 : (2 : K) ≠ 0) (hQ : (PoincareGraph.Bundles.poincareGraphBundle D p).IsAmple) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincareAt p) := by
  obtain ⟨M, hM, ⟨o⟩, ⟨e⟩⟩ := exists_ample_graphTensorSquare_descent D p hs h2 hQ
  let q : A.scheme ⟶ D.abelian.scheme := Picard.PoincareBundle.InducingMap.hom D M
  let : IsMonHom q := Picard.PoincareBundle.InducingMap.hom_isMonHom D M
  obtain ⟨c⟩ := Picard.PoincareBundle.InducingMap.exists_familyIso D M o
  rw [tensorHom_id] at c
  let eM : (((D.poincareAt q).tensor (M.pullback (fst A.scheme A.scheme).left)).tensor
      (M.pullback (snd A.scheme A.scheme).left)).sheaf ≅
        (M.pullback μ[A.scheme].left).sheaf :=
    Tensor.ProductSheaf.tensorModuleCongr (Tensor.ProductSheaf.tensorModuleCongr c.symm (Iso.refl _)) (Iso.refl _) ≪≫
      Picard.PoincareBundle.InducingClass.Bundle.formula A.scheme M
  have h4 : (4 : K) ≠ 0 := by
    simpa only [show (2 : K) * 2 = 4 by norm_num] using mul_ne_zero h2 h2
  have hqp : q = p := SymmetricGraphDescentCancellation.hom_eq_of_graphTensorSquare_descent D p q hs h4 M eM e
  have hp : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincareAt q) :=
    ⟨M, hM, ⟨o⟩, ⟨eM⟩⟩
  exact hqp ▸ hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricAmpleGraphPositivity
