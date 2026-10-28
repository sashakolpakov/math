import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.Rigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Constant Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantMaps.FieldDescent

noncomputable section

/-! A group endomorphism of a constant abelian family over an integral
parameter scheme comes from a group endomorphism over the ground field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons
variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (Y : Over (Spec (.of k)))

omit [IsAlgClosed k] in
private theorem baseChange_unit_fst :
    η[(Over.pullback Y.hom).obj A.scheme].left ≫ pullback.fst A.scheme.hom Y.hom =
      Y.hom ≫ η[A.scheme].left := by
  have h := congrArg (fun z => z.left)
    ((A.baseChangePointsMulEquiv Y.hom (𝟙_ (Over Y.left))).map_one)
  exact h

def constantFamilyMap
    (a : (Over.pullback Y.hom).obj A.scheme ⟶ (Over.pullback Y.hom).obj A.scheme) :
    Y ⊗ A.scheme ⟶ A.scheme :=
  Over.homMk ((pullbackSymmetry Y.hom A.scheme.hom).hom ≫
    a.left ≫ pullback.fst A.scheme.hom Y.hom) (by
      have hw : a.left ≫ pullback.snd A.scheme.hom Y.hom =
          pullback.snd A.scheme.hom Y.hom := a.w
      rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc a.left, hw, ← Category.assoc, pullbackSymmetry_hom_comp_snd]
      rfl)

omit [IsAlgClosed k] in
private theorem constantFamilyMap_pointed
    (a : (Over.pullback Y.hom).obj A.scheme ⟶ (Over.pullback Y.hom).obj A.scheme) [IsMonHom a] :
    lift (𝟙 Y) (toUnit Y ≫ η[A.scheme]) ≫ constantFamilyMap A Y a = 1 := by
  let z := lift (𝟙 Y) (toUnit Y ≫ η[A.scheme])
  have hz : z.left ≫ (pullbackSymmetry Y.hom A.scheme.hom).hom =
      η[(Over.pullback Y.hom).obj A.scheme].left := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, baseChange_unit_fst]
      exact congrArg (fun f => f.left) (lift_snd (𝟙 Y) (toUnit Y ≫ η[A.scheme]))
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
      exact (congrArg (fun f => f.left) (lift_fst (𝟙 Y)
        (toUnit Y ≫ η[A.scheme]))).trans (Over.w η[(Over.pullback Y.hom).obj A.scheme]).symm
  apply Over.OverMorphism.ext
  change z.left ≫ ((pullbackSymmetry Y.hom A.scheme.hom).hom ≫
    a.left ≫ pullback.fst A.scheme.hom Y.hom) = Y.hom ≫ η[A.scheme].left
  rw [← Category.assoc, hz, ← Category.assoc]
  have ha := congrArg (fun f => f.left) (IsMonHom.one_hom a)
  simp only [Over.comp_left] at ha
  rw [ha, baseChange_unit_fst]

theorem constantFamily_endomorphism_descends
    [LocallyOfFiniteType Y.hom] [IsIntegral Y.left]
    (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (a : (Over.pullback Y.hom).obj A.scheme ⟶ (Over.pullback Y.hom).obj A.scheme) [IsMonHom a] :
    ∃ f : A.scheme ⟶ A.scheme, IsMonHom f ∧ (Over.pullback Y.hom).map f = a := by
  obtain ⟨f, hf, he⟩ := Abelian.Rigidity.FieldDescent.pointedAbelianFamily_eq_fiber Y A.scheme A.scheme y₀
    (constantFamilyMap A Y a) (constantFamilyMap_pointed A Y a)
  refine ⟨f, hf, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply (cancel_epi (pullbackSymmetry Y.hom A.scheme.hom).hom).mp
    have hh := congrArg (fun f => f.left) he
    change (pullbackSymmetry Y.hom A.scheme.hom).hom ≫
      a.left ≫ pullback.fst A.scheme.hom Y.hom = pullback.snd Y.hom A.scheme.hom ≫ f.left at hh
    rw [HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst]
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact hh.symm
  · exact ((Over.pullback Y.hom).map f).w.trans a.w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantMaps.FieldDescent
