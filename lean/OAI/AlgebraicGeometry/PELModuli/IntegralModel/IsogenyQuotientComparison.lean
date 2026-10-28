import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyQuotient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.KernelBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.BaseChangeComparisons
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientUniqueness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.KernelComparison

/-! # Isogeny Quotient Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Identify the constructed arithmetic quotient with the original complex
isogeny target. The full kernel comparison and fpqc quotient uniqueness
construct the actual group-scheme isomorphism and identify the exact map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  {A : Over (Spec (.of K))} [GrpObj A]
  {C : Over (Spec (.of ℂ))} [GrpObj C]
  {f : (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A ⟶ C} [IsMonHom f]

section

variable (D : Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient κ A f)

def Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexTarget : Over (Spec (.of ℂ)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj D.target.toOver

instance Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexTarget_group : GrpObj D.complexTarget :=
  inferInstanceAs (GrpObj ((Over.pullback
    (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj D.target.toOver))

def Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexBaseChangedQuotient :
    (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj
      ((Over.pullback D.baseExtension.fieldExtension).obj A) ⟶ D.complexTarget :=
  (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).map D.quotient

instance Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexBaseChangedQuotient_isMonHom : IsMonHom D.complexBaseChangedQuotient :=
  Functor.map.instIsMonHom
    (F := Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding)))
    (f := D.quotient) ((Over.pullback D.baseExtension.fieldExtension).obj A) D.target.toOver

def Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexSourceMap : (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A ⟶
    (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj
      ((Over.pullback D.baseExtension.fieldExtension).obj A) :=
  (Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso D.baseExtension A).inv

instance Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexSourceMap_isMonHom : IsMonHom D.complexSourceMap := by
  unfold Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexSourceMap
  infer_instance

def Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexSourceHom :
    (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj
      ((Over.pullback D.baseExtension.fieldExtension).obj A) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A :=
  (Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso D.baseExtension A).hom

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexSourceHom_sourceMap : D.complexSourceHom ≫ D.complexSourceMap = 𝟙 _ :=
  Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso_hom_inv_id D.baseExtension A

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexSourceMap_sourceHom : D.complexSourceMap ≫ D.complexSourceHom = 𝟙 _ :=
  Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso_inv_hom_id D.baseExtension A

def Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexSourceIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj
      ((Over.pullback D.baseExtension.fieldExtension).obj A) ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A :=
  ⟨D.complexSourceHom, D.complexSourceMap, D.complexSourceHom_sourceMap, D.complexSourceMap_sourceHom⟩

def Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexQuotient : (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A ⟶ D.complexTarget :=
  D.complexSourceMap ≫
    D.complexBaseChangedQuotient

instance Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexQuotient_isMonHom : IsMonHom D.complexQuotient := by
  unfold Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexQuotient
  infer_instance

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexQuotient_eq : D.complexQuotient =
    D.complexSourceMap ≫
      D.complexBaseChangedQuotient := rfl

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexKernelMap : D.complexKernelIso.hom ≫
    (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).map D.inclusion ≫
      D.complexSourceIso.hom = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f := by
  let ψ := Spec.map (CommRingCat.ofHom D.baseExtension.embedding)
  let σ := D.complexSourceIso
  let m := (Over.pullback ψ).map D.inclusion
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((D.complexKernelIso.hom.left ≫ m.left ≫ σ.hom.left) ≫
      pullback.fst A.hom (Spec.map (CommRingCat.ofHom κ))) = _
    calc
      _ = D.complexKernelIso.hom.left ≫ m.left ≫
          pullback.fst (pullback.snd A.hom D.baseExtension.fieldExtension) ψ ≫
            pullback.fst A.hom D.baseExtension.fieldExtension := by
        exact (Category.assoc _ _ _).trans
          (congrArg (fun a => D.complexKernelIso.hom.left ≫ a)
            ((Category.assoc _ _ _).trans (congrArg (fun a => m.left ≫ a)
              (Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso_fst D.baseExtension A))))
      _ = D.complexKernelIso.hom.left ≫ pullback.fst D.subgroup.hom ψ ≫
          D.inclusion.left ≫ pullback.fst A.hom D.baseExtension.fieldExtension := by
        exact congrArg (fun a => D.complexKernelIso.hom.left ≫ a)
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun a => a ≫ pullback.fst A.hom D.baseExtension.fieldExtension)
              (AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst D.inclusion ψ)).trans (Category.assoc _ _ _)))
      _ = _ := D.kernelComparison
  · exact (D.complexKernelIso.hom ≫ m ≫ σ.hom).w.trans (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f).w.symm

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.baseChangedQuotient_kernel (T : Over (Spec (.of ℂ)))
    (x : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj
      ((Over.pullback D.baseExtension.fieldExtension).obj A)) :
    x ≫ D.complexBaseChangedQuotient = 1 ↔
      ∃ r : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj D.subgroup,
        r ≫ (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).map D.inclusion = x :=
  Group.KernelBaseChange.GroupPoints.kernel_baseChange (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))
    D.quotient D.inclusion D.kernel T x

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexQuotient_kernel_presentation (T : Over (Spec (.of ℂ)))
    (x : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A) :
    x ≫ D.complexQuotient = 1 ↔
      ∃ r : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).obj D.subgroup,
        r ≫ (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).map D.inclusion =
          x ≫ D.complexSourceMap := by
  rw [D.complexQuotient_eq, ← Category.assoc]
  exact D.baseChangedQuotient_kernel T _

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexQuotient_kernel_image (T : Over (Spec (.of ℂ)))
    (x : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A) :
    x ≫ D.complexQuotient = 1 ↔
      ∃ z : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f, z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = x := by
  let σ := D.complexSourceIso
  let γ := D.complexKernelIso
  let j := (Over.pullback (Spec.map (CommRingCat.ofHom D.baseExtension.embedding))).map D.inclusion
  rw [D.complexQuotient_kernel_presentation]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r ≫ γ.inv, ?_⟩
    have hγ : γ.hom ≫ j ≫ σ.hom = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f := D.complexKernelMap
    rw [← hγ, Category.assoc, γ.inv_hom_id_assoc, ← Category.assoc, hr]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => x ≫ a) σ.inv_hom_id).trans (Category.comp_id x))
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ γ.hom, ?_⟩
    apply (cancel_mono σ.hom).mp
    calc
      _ = z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f :=
        (Category.assoc _ _ _).trans
          ((Category.assoc _ _ _).trans (congrArg (fun a => z ≫ a) D.complexKernelMap))
      _ = x := hz
      _ = (x ≫ σ.inv) ≫ σ.hom := by simp only [Category.assoc, σ.inv_hom_id, Category.comp_id]

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complexQuotient_kernel (T : Over (Spec (.of ℂ)))
    (x : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj A) :
    x ≫ D.complexQuotient = 1 ↔ x ≫ f = 1 :=
  (D.complexQuotient_kernel_image T x).trans (KernelComparison.kernel_inclusion_classifies f T x).symm

theorem Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient.complex_target_iso [IsFinite f.left] [Etale f.left] [Surjective f.left] :
    ∃ e : D.complexTarget ≅ C, IsMonHom e.hom ∧ D.complexQuotient ≫ e.hom = f := by
  let ψ := Spec.map (CommRingCat.ofHom D.baseExtension.embedding)
  let σ := D.complexSourceIso
  let p := (Over.pullback ψ).map D.quotient
  have : IsIso σ.inv.left := inferInstanceAs
    (IsIso (((Over.forget (Spec (.of ℂ))).mapIso σ).inv))
  have : IsFinite p.left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback ψ D.quotient).flip D.finite
  have : Flat p.left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback ψ D.quotient).flip D.flat
  have : Surjective p.left := MorphismProperty.of_isPullback
    (ArithmeticGeometry.Models.FoundationsPullback.Constructions.pullback_over_map_isPullback ψ D.quotient).flip D.surjective
  have : IsFinite D.complexQuotient.left := inferInstanceAs (IsFinite (σ.inv.left ≫ p.left))
  have : Flat D.complexQuotient.left := inferInstanceAs (Flat (σ.inv.left ≫ p.left))
  have : Surjective D.complexQuotient.left := inferInstanceAs (Surjective (σ.inv.left ≫ p.left))
  exact QuotientUniqueness.quotient_group_iso_of_same_kernel D.complexQuotient f D.complexQuotient_kernel

end

variable [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [IsFinite f.left] [Etale f.left] [Surjective f.left]

/-- An isogeny target of an arithmetic abelian variety has an effective
arithmetic group model and an exact comparison of the original isogeny. -/
theorem IsogenyQuotientComparison.finite_etale_isogeny_target_descends (N : ℕ) (hN : N ≠ 0) :
    ∃ D : Arithmetic.IsogenyQuotient.ArithmeticIsogenyQuotient κ A f, D.baseExtension.denominator = N ∧
      ∃ e : D.complexTarget ≅ C, IsMonHom e.hom ∧ D.complexQuotient ≫ e.hom = f := by
  obtain ⟨D, hD⟩ := Arithmetic.IsogenyQuotient.arithmetic_isogeny_quotient_exists κ A f N hN
  exact ⟨D, hD, D.complex_target_iso⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
