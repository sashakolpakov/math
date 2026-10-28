import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberBilinearComposition

/-! # Parameter Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterRecovery

noncomputable section

/-!
# A global product on the parameter scheme defines all actual fiber products
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

variable {S : Scheme.{u}} {A X : Over S}

/-- The genuine parameter point associated with two product inputs. -/
def parameter {T : Over S} (a b : T ⟶ A ⊗ X) : T ⟶ (A ⊗ A) ⊗ X :=
  lift (lift (a ≫ fst A X) (b ≫ fst A X)) (a ≫ snd A X)

/-- The parameter point recovers its first input. -/
theorem parameter_left {T : Over S} (a b : T ⟶ A ⊗ X) : parameter a b ≫ ParameterSchemes.inputLeft A X = a := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [parameter, ParameterSchemes.inputLeft]

/-- Equal fixed coordinates make the same parameter point recover its second input. -/
theorem parameter_right {T : Over S} (a b : T ⟶ A ⊗ X) (h : a ≫ snd A X = b ≫ snd A X) :
    parameter a b ≫ ParameterSchemes.inputRight A X = b := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [parameter, ParameterSchemes.inputRight, h]

/-- Parameter points commute with every change of test scheme. -/
theorem parameter_comp {T U : Over S} (t : U ⟶ T) (a b : T ⟶ A ⊗ X) :
    t ≫ parameter a b = parameter (t ≫ a) (t ≫ b) := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext <;> simp [parameter, Category.assoc]
  · simp [parameter, Category.assoc]

variable [GrpObj A]

/-- The actual product relation makes the output of the parameter point precisely the specified product. -/
theorem parameter_output {T : Over S} (a b c : T ⟶ A ⊗ X) (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) :
    parameter a b ≫ ParameterSchemes.outputPoint A X = c := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa [parameter, ParameterSchemes.outputPoint, Category.assoc, MonObj.comp_mul] using h.1
  · simpa [parameter, ParameterSchemes.outputPoint, Category.assoc] using h.2.2

variable (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (ParameterSchemes.inputLeft A X)) (Line.Fibers.fiber L (ParameterSchemes.inputRight A X)) (Line.Fibers.fiber L (ParameterSchemes.outputPoint A X)))

/-- The actual fiber product associated with the single global product map. -/
def product {T : Over S} (a b c : T ⟶ A ⊗ X) (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L a) (Line.Fibers.fiber L b) (Line.Fibers.fiber L c) :=
  Line.Fibers.pullBilinear L (parameter a b) (ParameterSchemes.inputLeft A X) (ParameterSchemes.inputRight A X) (ParameterSchemes.outputPoint A X) a b c
    (parameter_left a b) (parameter_right a b h.2.1) (parameter_output a b c h) β

/-- Invertibility of the genuine global product implies invertibility on every test-scheme fiber. -/
theorem product_isIso (hβ : IsIso (Bilinear.BilinearPullback.toHom β))
    {T : Over S} (a b c : T ⟶ A ⊗ X) (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) :
    IsIso (Bilinear.BilinearPullback.toHom (ParameterRecovery.product L β a b c h)) := by
  have hp : IsIso (Bilinear.BilinearPullback.toHom
      (Bilinear.BilinearPullback.pullback (parameter a b).left
        (Line.Fibers.fiber_isLine L (ParameterSchemes.inputLeft A X)) (Line.Fibers.fiber_isLine L (ParameterSchemes.inputRight A X)) β)) := by
    rw [Bilinear.BilinearPullback.toHom_pullback]
    unfold Bilinear.BilinearPullback.pulledHom
    infer_instance
  unfold ParameterRecovery.product Line.Fibers.pullBilinear
  rw [Bilinear.Transport.toHom_transport]
  infer_instance

omit [GrpObj A] in
/-- Equal parameter maps induce the same actual fiber product, with all composition proofs retained. -/
theorem pullBilinear_congr {T K : Over S} (p q : T ⟶ K) (hpq : p = q)
    (a b c : K ⟶ A ⊗ X) (a' b' c' : T ⟶ A ⊗ X)
    (ha : p ≫ a = a') (hb : p ≫ b = b') (hc : p ≫ c = c')
    (ha' : q ≫ a = a') (hb' : q ≫ b = b') (hc' : q ≫ c = c')
    (γ : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L a) (Line.Fibers.fiber L b) (Line.Fibers.fiber L c)) :
    Line.Fibers.pullBilinear L p a b c a' b' c' ha hb hc γ = Line.Fibers.pullBilinear L q a b c a' b' c' ha' hb' hc' γ := by
  cases hpq
  rfl

/-- The fiber products recovered from a global product commute with every test-scheme pullback. -/
theorem product_natural {T U : Over S} (t : U ⟶ T) (a b c : T ⟶ A ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) (a' b' c' : U ⟶ A ⊗ X)
    (h' : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a' b' c')
    (ha : t ≫ a = a') (hb : t ≫ b = b') (hc : t ≫ c = c') :
    Line.Fibers.pullBilinear L t a b c a' b' c' ha hb hc (ParameterRecovery.product L β a b c h) = ParameterRecovery.product L β a' b' c' h' := by
  have hp : t ≫ parameter a b = parameter a' b' := by rw [parameter_comp, ha, hb]
  unfold ParameterRecovery.product
  rw [FiberBilinearComposition.pullBilinear_comp
    (hx'' := (congrArg (fun v => v ≫ ParameterSchemes.inputLeft A X) hp).trans (parameter_left a' b'))
    (hy'' := (congrArg (fun v => v ≫ ParameterSchemes.inputRight A X) hp).trans (parameter_right a' b' h'.2.1))
    (hz'' := (congrArg (fun v => v ≫ ParameterSchemes.outputPoint A X) hp).trans (parameter_output a' b' c' h'))]
  exact pullBilinear_congr L _ _ hp _ _ _ _ _ _ _ _ _ _ _ _ β

/-- Applying universal recovery to an existing genuine multiplication recovers that multiplication exactly. -/
theorem product_global (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)
    {T : Over S} (a b c : T ⟶ A ⊗ X) (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) :
    ParameterRecovery.product L (ParameterSchemes.globalProduct A X L D) a b c h = D.product a b c h :=
  D.product_natural (parameter a b) (ParameterSchemes.inputLeft A X) (ParameterSchemes.inputRight A X) (ParameterSchemes.outputPoint A X)
    (ParameterSchemes.productRelation A X) a b c h (parameter_left a b) (parameter_right a b h.2.1) (parameter_output a b c h)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterRecovery
