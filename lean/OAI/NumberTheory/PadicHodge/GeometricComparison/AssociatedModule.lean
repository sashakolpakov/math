import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange

/-! # Associated Module -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AssociatedModule.AssociatedModuleCech

noncomputable section

/-! Actual associated module sheaves have vanishing positive Čech cohomology on finite principal affine covers, also after exact coefficient restriction. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u v w

variable (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
  {ι : Type u} [Finite ι] (s : ι → A) (hs : Ideal.span (Set.range s) = ⊤)

include hs in
theorem exactAt_succ (n : ℕ) :
    ((cechComplexFunctor (fun i => (PrimeSpectrum.basicOpen (s i) : (Spec A).Opens))).obj
      (modulesSpecToSheaf.obj (tilde (R := A) M)).obj).ExactAt (n + 1) := by
  let P := (modulesSpecToSheaf.obj (tilde (R := A) M)).obj
  let f := AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation A (AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech.model A)
    (fun i => AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization.AffineIntersectionLocalization.principal A (s i)) P
  have ha : QuasiIso f := AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech.tilde_quasiIso A s M hs
  have hz : ((CochainComplex.single₀ (ModuleCat A)).obj (P.obj (op ⊤))).ExactAt (n + 1) :=
    HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (P.obj (op ⊤))
        (n + 1) (Nat.succ_ne_zero n))
  exact (quasiIsoAt_iff_exactAt f (n + 1) hz).mp (ha.quasiIsoAt (n + 1))

variable {D : Type v} [Category.{w} D] [Abelian D] [HasProducts.{u} D]
  (G : ModuleCat.{u} A ⥤ D) [G.Additive] [G.PreservesHomology]
  [PreservesLimitsOfSize.{u, u} G]

include hs in
theorem comp_exactAt_succ (n : ℕ) :
    ((cechComplexFunctor (fun i => (PrimeSpectrum.basicOpen (s i) : (Spec A).Opens))).obj
      ((modulesSpecToSheaf.obj (tilde (R := A) M)).obj ⋙ G)).ExactAt (n + 1) := by
  let U := fun i => (PrimeSpectrum.basicOpen (s i) : (Spec A).Opens)
  let P := (modulesSpecToSheaf.obj (tilde (R := A) M)).obj
  let K := (cechComplexFunctor U).obj P
  have hK := exactAt_succ A M s hs n
  have hm : ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)] at hK ⊢
    exact hK.map G
  exact hm.of_iso (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G (FormalCoproduct.mk ι U).cech P)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AssociatedModule.AssociatedModuleCech
