import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyKernelTorsion
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleSubgroupDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplementGeometry
import OAI.ArithmeticGeometry.Models.FoundationsPullback

/-! # Isogeny Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyKernel

noncomputable section

/-! The scheme-theoretic kernel of a complex finite étale isogeny out of
an arithmetic abelian variety has an actual arithmetic closed subgroup
model. Its torsion bound, embedding into arithmetic torsion, finite-extension
model, and exact complex group comparison are all constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom]
  {C : Over (Spec (.of ℂ))} [GrpObj C]

/-- The kernel model is constructed from the isogeny itself, without
assuming an annihilator, algebraic coordinates, or a descended subgroup. -/
theorem finite_etale_isogeny_kernel_descends
    (f : (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A ⟶ C)
    [IsMonHom f] [IsFinite f.left] [Etale f.left] (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ), B.denominator = N ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G),
        ∃ (j : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G ⟶
            (Over.pullback B.fieldExtension).obj A)
          (q : (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).left ⟶ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).left)
          (γ : Picard.PoincareBundle.Kernel.Scheme.kernelObject f ≅ (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj
            (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G)),
          IsMonHom j ∧ IsClosedImmersion j.left ∧ IsMonHom γ.hom ∧
            IsFinite (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ∧
            Etale (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom ∧
            γ.hom.left ≫ pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom
              (Spec.map (CommRingCat.ofHom B.embedding)) = q ∧
            IsPullback q (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of B.extension.carrier)) G).hom
              (Spec.map (CommRingCat.ofHom B.embedding)) ∧
            q ≫ j.left ≫ pullback.fst A.hom B.fieldExtension =
              (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f).left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom κ)) := by
  obtain ⟨n, hn, hker⟩ := IsogenyComplement.finite_etale_kernel_annihilated f
  have hT := AbelianScheme.TorsionQuotient.Etale.TorsionEtale.torsion_finite_etale A n (IsogenyComplementGeometry.integer_unit_at_field_stalk n hn)
  let := hT.1
  let := hT.2
  have : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite f
  have : Etale (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom := IsogenyKernelTorsion.kernel_etale f
  let i := IsogenyKernelTorsion.kernelIntoArithmeticTorsion A (Spec.map (CommRingCat.ofHom κ)) f n hker
  obtain ⟨B, hBN, G, hG, hfin, jT, _, q, hjT, hjClosed, _, hFinite, hEtale, hcart, hmap,
      γ, hγ, hγq⟩ := IntegralModel.Finite.EtaleSubgroupDescent.finite_etale_subgroup_descends κ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n) (Picard.PoincareBundle.Kernel.Scheme.kernelObject f) i N hN
  let := hjT
  let := hjClosed
  let F := Over.pullback B.fieldExtension
  let j := jT ≫ F.map (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)
  have hι : IsClosedImmersion (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left := AbelianScheme.TorsionQuotient.Quasi.TorsionGeometry.torsion_closedImmersion A n
  have hιL : IsClosedImmersion (F.map (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).left :=
    MorphismProperty.of_isPullback
      (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback B.fieldExtension (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).flip hι
  have hj : IsClosedImmersion j.left := inferInstanceAs
    (IsClosedImmersion (jT.left ≫ (F.map (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).left))
  have hjGroup : IsMonHom j := inferInstanceAs (IsMonHom (jT ≫ F.map (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)))
  have hcompare : q ≫ j.left ≫ pullback.fst A.hom B.fieldExtension =
      (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f).left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom κ)) := by
    change q ≫ (jT.left ≫ (F.map (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n)).left) ≫ pullback.fst A.hom B.fieldExtension = _
    calc
      _ = q ≫ jT.left ≫ pullback.fst (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom B.fieldExtension ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left :=
        (Category.assoc _ _ _).trans
          (congrArg (fun a => q ≫ a) ((Category.assoc _ _ _).trans
            (congrArg (fun a => jT.left ≫ a) (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n) B.fieldExtension))))
      _ = i.left ≫ pullback.fst (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom (Spec.map (CommRingCat.ofHom κ)) ≫
          (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A n).left) hmap
      _ = _ := IsogenyKernelTorsion.kernelIntoArithmeticTorsion_inclusion A (Spec.map (CommRingCat.ofHom κ)) f n hker
  exact ⟨B, hBN, G, hG, hfin, j, q, γ, hjGroup, hj, hγ, hFinite, hEtale, hγq, hcart, hcompare⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyKernel
