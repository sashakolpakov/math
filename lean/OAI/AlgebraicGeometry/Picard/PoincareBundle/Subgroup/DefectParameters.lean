import OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.ProductDefect
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductUnitNaturality

/-! # Defect Parameters -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters

noncomputable section

/-! Properness makes the translation defect depend only on the two subgroup parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.NormalizedKernelTranslation OAI.AlgebraicGeometry.Picard.PoincareBundle.ProperProductLineUnits

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H A : Over (Spec (.of k))} [GrpObj H] [IsCommMonObj H] [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]
  (i : H ⟶ A) [IsMonHom i] (L : Line.Bundles.LineBundle A.left)
  (t : Line.Fibers.fiber L (snd H A) ≅ Line.Fibers.fiber L (NormalizedKernelTranslation.action i))

/-- The actual defect on the universal pair of subgroup elements and a varying starting point. -/
def universalUnit : Γ(((H ⊗ H) ⊗ A).left, ⊤)ˣ :=
  ProductDefect.value i L t
    (fst (H ⊗ H) A ≫ fst H H) (fst (H ⊗ H) A ≫ snd H H) (snd (H ⊗ H) A)

/-- Its unique regular coefficient on the subgroup product. -/
def coefficient : Γ((H ⊗ H).left, ⊤)ˣ := ProperProductLineUnits.baseUnit (H ⊗ H) A (universalUnit i L t)

/-- Evaluate the regular coefficient on any pair of subgroup points. -/
def value {T : Over (Spec (.of k))} (a b : T ⟶ H) : Γ(T.left, ⊤)ˣ :=
  Units.map (lift a b).left.appTop.hom.toMonoidHom (coefficient i L t)

theorem value_natural {T U : Over (Spec (.of k))} (g : U ⟶ T) (a b : T ⟶ H) :
    Units.map g.left.appTop.hom.toMonoidHom (value i L t a b) = value i L t (g ≫ a) (g ≫ b) := by
  apply Units.ext
  change (g ≫ lift a b).left.appTop (coefficient i L t).val =
    (lift (g ≫ a) (g ≫ b)).left.appTop (coefficient i L t).val
  rw [comp_lift]

/-- The defect is independent of the starting point, on every test scheme, including nonreduced ones. -/
theorem defect_eq_value {T : Over (Spec (.of k))} (a b : T ⟶ H) (x : T ⟶ A) :
    ProductDefect.value i L t a b x = value i L t a b := by
  let q : T ⟶ (H ⊗ H) ⊗ A := lift (lift a b) x
  have hqa : q ≫ (fst (H ⊗ H) A ≫ fst H H) = a := by
    rw [← Category.assoc, lift_fst, lift_fst]
  have hqb : q ≫ (fst (H ⊗ H) A ≫ snd H H) = b := by
    rw [← Category.assoc, lift_fst, lift_snd]
  have hqx : q ≫ snd (H ⊗ H) A = x := lift_snd _ _
  have hn := ProductDefect.value_natural i L t q
    (fst (H ⊗ H) A ≫ fst H H) (fst (H ⊗ H) A ≫ snd H H) (snd (H ⊗ H) A)
  rw [hqa, hqb, hqx] at hn
  have hf := ProperProductLineUnits.pullback_baseUnit (H ⊗ H) A (universalUnit i L t)
  calc
    ProductDefect.value i L t a b x =
        Units.map q.left.appTop.hom.toMonoidHom (universalUnit i L t) := hn
    _ = Units.map q.left.appTop.hom.toMonoidHom
        (Units.map (fst (H ⊗ H) A).left.appTop.hom.toMonoidHom (coefficient i L t)) :=
      congrArg (Units.map q.left.appTop.hom.toMonoidHom) hf.symm
    _ = value i L t a b := by
      apply Units.ext
      change (q ≫ fst (H ⊗ H) A).left.appTop (coefficient i L t).val =
        (lift a b).left.appTop (coefficient i L t).val
      rw [lift_fst]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Subgroup.DefectParameters
