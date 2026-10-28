import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.TotalMaps

/-! # Total Group Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TotalGroupMaps

noncomputable section

section

/-! Actual total-space maps on the dual family induced by polarized
comparisons. Identity and composition use the original full polarized
comparisons, so no marking or polarization on the dual is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S T U : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (f : T ⟶ S) (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f))

def dualTotalMap : B.dual.abelian.scheme.left ⟶ A.dual.abelian.scheme.left :=
  e.dual.hom.left ≫ pullback.fst A.dual.abelian.scheme.hom f

theorem dualTotalMap_base :
    dualTotalMap A B f e ≫ A.dual.abelian.scheme.hom = B.dual.abelian.scheme.hom ≫ f := by
  change (e.dual.hom.left ≫ pullback.fst A.dual.abelian.scheme.hom f) ≫ A.dual.abelian.scheme.hom = _
  exact (Category.assoc e.dual.hom.left (pullback.fst A.dual.abelian.scheme.hom f)
    A.dual.abelian.scheme.hom).trans
    ((congrArg (fun q => e.dual.hom.left ≫ q) (pullback.condition (f := A.dual.abelian.scheme.hom)
      (g := f))).trans
      ((Category.assoc e.dual.hom.left (pullback.snd A.dual.abelian.scheme.hom f) f).symm.trans
        (congrArg (fun q => q ≫ f) e.dual.hom.w)))

theorem dualTotalMap_isPullback :
    IsPullback (dualTotalMap A B f e) B.dual.abelian.scheme.hom A.dual.abelian.scheme.hom f :=
  IsPullback.of_iso_pullback ⟨dualTotalMap_base A B f e⟩
    ((Over.forget T).mapIso e.dual) rfl e.dual.hom.w

theorem dualTotalMap_id :
    dualTotalMap A A (𝟙 S) (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackId A).symm =
      𝟙 A.dual.abelian.scheme.left := by
  change A.dual.abelian.pullbackIdIso.inv.left ≫ pullback.fst A.dual.abelian.scheme.hom (𝟙 S) = _
  rw [← A.dual.abelian.pullbackIdIso_hom_left]
  exact ((Over.forget S).mapIso A.dual.abelian.pullbackIdIso).inv_hom_id

theorem dualTotalMap_eq_of_base_eq {f' : T ⟶ S} (h : f = f')
    (d : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f'))
    [Subsingleton (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f))] :
    dualTotalMap A B f e = dualTotalMap A B f' d := by
  cases h
  exact congrArg (dualTotalMap A B f) (Subsingleton.elim e d)

theorem dualTotalMap_comp
    (C : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N U)
    (h : U ⟶ T) (d : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso C (B.pullback h)) :
    dualTotalMap A C (h ≫ f)
        (d.trans ((e.pullback h).trans (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A f h))) =
      dualTotalMap B C h d ≫ dualTotalMap A B f e := by
  change (d.dual.hom.left ≫ ((Over.pullback h).map e.dual.hom).left ≫
      (A.dual.abelian.pullbackCompIso f h).inv.left) ≫ pullback.fst A.dual.abelian.scheme.hom (h ≫ f) =
    (d.dual.hom.left ≫ pullback.fst B.dual.abelian.scheme.hom h) ≫
      (e.dual.hom.left ≫ pullback.fst A.dual.abelian.scheme.hom f)
  exact Polarized.TotalMaps.totalMap_comparison_composition d.dual.hom.left
    ((Over.pullback h).map e.dual.hom).left (A.dual.abelian.pullbackCompIso f h).inv.left
    (pullback.fst A.dual.abelian.scheme.hom (h ≫ f))
    (pullback.fst (A.dual.abelian.pullback f).scheme.hom h) (pullback.fst A.dual.abelian.scheme.hom f)
    (pullback.fst B.dual.abelian.scheme.hom h) e.dual.hom.left
    (A.dual.abelian.pullbackCompIso_inv_left_fst f h) (HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst e.dual.hom h)

end

/-! The dual parts of polarized comparisons preserve the actual
identity, inverse, and multiplication maps on total spaces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (f : T ⟶ S) (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f))

def dualTotalPoints (V : Over T) :
    (V ⟶ B.dual.abelian.scheme) →* ((Over.map f).obj V ⟶ A.dual.abelian.scheme) :=
  (A.dual.abelian.baseChangePointsMulEquiv f V).toMonoidHom.comp
    (IsMonHom.monoidHom e.dual.hom V)

theorem dualTotalPoints_left (V : Over T) (x : V ⟶ B.dual.abelian.scheme) :
    (dualTotalPoints A B f e V x).left = x.left ≫ dualTotalMap A B f e :=
  Category.assoc x.left e.dual.hom.left (pullback.fst A.dual.abelian.scheme.hom f)

theorem dualTotalMap_zero :
    η[B.dual.abelian.scheme].left ≫ dualTotalMap A B f e = f ≫ η[A.dual.abelian.scheme].left := by
  have h := congrArg Over.Hom.left (map_one (dualTotalPoints A B f e (𝟙_ (Over T))))
  rw [dualTotalPoints_left] at h
  simp only [Hom.one_def, Over.comp_left, Over.toUnit_left] at h
  change ((𝟙 T ≫ η[B.dual.abelian.scheme].left) ≫ dualTotalMap A B f e) =
    (𝟙 T ≫ f) ≫ η[A.dual.abelian.scheme].left at h
  simpa only [Category.id_comp] using h

theorem dualTotalMap_inv :
    (GrpObj.inv : B.dual.abelian.scheme ⟶ B.dual.abelian.scheme).left ≫ dualTotalMap A B f e =
      dualTotalMap A B f e ≫ (GrpObj.inv : A.dual.abelian.scheme ⟶ A.dual.abelian.scheme).left := by
  have h := congrArg Over.Hom.left
    (map_inv (dualTotalPoints A B f e B.dual.abelian.scheme) (𝟙 B.dual.abelian.scheme))
  rw [dualTotalPoints_left] at h
  simpa only [Hom.inv_def, Over.comp_left, Over.id_left, Category.id_comp,
    dualTotalPoints_left] using h

def dualTotalPairMap : (B.dual.abelian.scheme ⊗ B.dual.abelian.scheme).left ⟶
    (A.dual.abelian.scheme ⊗ A.dual.abelian.scheme).left :=
  (lift (dualTotalPoints A B f e _ (fst B.dual.abelian.scheme B.dual.abelian.scheme))
    (dualTotalPoints A B f e _ (snd B.dual.abelian.scheme B.dual.abelian.scheme))).left

theorem dualTotalMap_mul :
    μ[B.dual.abelian.scheme].left ≫ dualTotalMap A B f e =
      dualTotalPairMap A B f e ≫ μ[A.dual.abelian.scheme].left := by
  have h := congrArg Over.Hom.left (map_mul (dualTotalPoints A B f e _)
    (fst B.dual.abelian.scheme B.dual.abelian.scheme) (snd B.dual.abelian.scheme B.dual.abelian.scheme))
  rw [dualTotalPoints_left] at h
  simp only [Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at h
  exact h

theorem dualTotalPairMap_fst :
    dualTotalPairMap A B f e ≫ (fst A.dual.abelian.scheme A.dual.abelian.scheme).left =
      (fst B.dual.abelian.scheme B.dual.abelian.scheme).left ≫ dualTotalMap A B f e := by
  exact (congrArg Over.Hom.left (lift_fst _ _)).trans (dualTotalPoints_left A B f e _ _)

theorem dualTotalPairMap_snd :
    dualTotalPairMap A B f e ≫ (snd A.dual.abelian.scheme A.dual.abelian.scheme).left =
      (snd B.dual.abelian.scheme B.dual.abelian.scheme).left ≫ dualTotalMap A B f e := by
  exact (congrArg Over.Hom.left (lift_snd _ _)).trans (dualTotalPoints_left A B f e _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TotalGroupMaps
