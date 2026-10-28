import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameters

/-! # Interchange Parameter Factors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameterFactors.Construction

noncomputable section

/-! The nine points of every actual test-scheme interchange square
factor through its four independent universal coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {S : Scheme.{u}} {G X T : Over S}

def lineInterchangeParameterLift (c a b : T ⟶ G ⊗ X) : T ⟶ InterchangeParameters.Construction.lineInterchangeParameter G X :=
  lift (lift (c ≫ fst G X) (b ≫ fst G X)) (lift (c ≫ snd G X) (a ≫ snd G X))

theorem lineInterchangeParameterLift_g1 (c a b : T ⟶ G ⊗ X) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangeG1 G X = c ≫ fst G X := by
  simp only [lineInterchangeParameterLift, InterchangeParameters.Construction.lineInterchangeG1, lift_fst_assoc, lift_fst]
theorem lineInterchangeParameterLift_g2 (c a b : T ⟶ G ⊗ X) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangeG2 G X = b ≫ fst G X := by
  simp only [lineInterchangeParameterLift, InterchangeParameters.Construction.lineInterchangeG2, lift_fst_assoc, lift_snd]
theorem lineInterchangeParameterLift_x1 (c a b : T ⟶ G ⊗ X) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangeX1 G X = c ≫ snd G X := by
  simp only [lineInterchangeParameterLift, InterchangeParameters.Construction.lineInterchangeX1, lift_snd_assoc, lift_fst]
theorem lineInterchangeParameterLift_x2 (c a b : T ⟶ G ⊗ X) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangeX2 G X = a ≫ snd G X := by
  simp only [lineInterchangeParameterLift, InterchangeParameters.Construction.lineInterchangeX2, lift_snd_assoc, lift_snd]

theorem lineInterchangeParameterLift_point (c a b d : T ⟶ G ⊗ X)
    (v : InterchangeParameters.Construction.lineInterchangeParameter G X ⟶ G) (t : InterchangeParameters.Construction.lineInterchangeParameter G X ⟶ X)
    (hv : lineInterchangeParameterLift c a b ≫ v = d ≫ fst G X)
    (ht : lineInterchangeParameterLift c a b ≫ t = d ≫ snd G X) :
    lineInterchangeParameterLift c a b ≫ lift v t = d := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [Category.assoc, lift_fst] using hv
  · simpa only [Category.assoc, lift_snd] using ht

theorem lineInterchangeParameterLift_pointC (c a b : T ⟶ G ⊗ X) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointC G X = c :=
  lineInterchangeParameterLift_point c a b c _ _ (lineInterchangeParameterLift_g1 c a b) (lineInterchangeParameterLift_x1 c a b)

theorem lineInterchangeParameterLift_pointA (c a b : T ⟶ G ⊗ X) (h : c ≫ fst G X = a ≫ fst G X) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointA G X = a :=
  lineInterchangeParameterLift_point c a b a _ _ ((lineInterchangeParameterLift_g1 c a b).trans h)
    (lineInterchangeParameterLift_x2 c a b)

theorem lineInterchangeParameterLift_pointB (c a b : T ⟶ G ⊗ X) (h : c ≫ snd G X = b ≫ snd G X) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointB G X = b :=
  lineInterchangeParameterLift_point c a b b _ _ (lineInterchangeParameterLift_g2 c a b)
    ((lineInterchangeParameterLift_x1 c a b).trans h)

theorem lineInterchangeParameterLift_pointX (c a b x : T ⟶ G ⊗ X)
    (hg : b ≫ fst G X = x ≫ fst G X) (ht : a ≫ snd G X = x ≫ snd G X) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointX G X = x :=
  lineInterchangeParameterLift_point c a b x _ _ ((lineInterchangeParameterLift_g2 c a b).trans hg)
    ((lineInterchangeParameterLift_x2 c a b).trans ht)

theorem lineInterchangeParameterLift_pointCA [GrpObj X] (c a b ca : T ⟶ G ⊗ X)
    (hca : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd G X) (fst G X) c a ca) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointCA G X = ca := by
  apply lineInterchangeParameterLift_point c a b ca _ _ ((lineInterchangeParameterLift_g1 c a b).trans hca.2.2)
  rw [MonObj.comp_mul, lineInterchangeParameterLift_x1, lineInterchangeParameterLift_x2]
  exact hca.1

theorem lineInterchangeParameterLift_pointCB [GrpObj G] (c a b cb : T ⟶ G ⊗ X)
    (hcb : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) c b cb) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointCB G X = cb := by
  apply lineInterchangeParameterLift_point c a b cb _ _ _ ((lineInterchangeParameterLift_x1 c a b).trans hcb.2.2)
  rw [MonObj.comp_mul, lineInterchangeParameterLift_g1, lineInterchangeParameterLift_g2]
  exact hcb.1

theorem lineInterchangeParameterLift_pointAX [GrpObj G] (c a b x ax : T ⟶ G ⊗ X)
    (hca : c ≫ fst G X = a ≫ fst G X) (hbx : b ≫ fst G X = x ≫ fst G X)
    (hax : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) a x ax) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointAX G X = ax := by
  apply lineInterchangeParameterLift_point c a b ax _ _ _ ((lineInterchangeParameterLift_x2 c a b).trans hax.2.2)
  rw [MonObj.comp_mul, lineInterchangeParameterLift_g1, lineInterchangeParameterLift_g2, hca, hbx]
  exact hax.1

theorem lineInterchangeParameterLift_pointBX [GrpObj X] (c a b x bx : T ⟶ G ⊗ X)
    (hcb : c ≫ snd G X = b ≫ snd G X) (hax : a ≫ snd G X = x ≫ snd G X)
    (hbx : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd G X) (fst G X) b x bx) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointBX G X = bx := by
  apply lineInterchangeParameterLift_point c a b bx _ _ ((lineInterchangeParameterLift_g2 c a b).trans hbx.2.2)
  rw [MonObj.comp_mul, lineInterchangeParameterLift_x1, lineInterchangeParameterLift_x2, hcb, hax]
  exact hbx.1

theorem lineInterchangeParameterLift_pointW [GrpObj G] [GrpObj X] (c a b cb ax w : T ⟶ G ⊗ X)
    (hcb : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst G X) (snd G X) c b cb) (hax : a ≫ snd G X = ax ≫ snd G X)
    (hby : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd G X) (fst G X) cb ax w) :
    lineInterchangeParameterLift c a b ≫ InterchangeParameters.Construction.lineInterchangePointW G X = w := by
  apply lineInterchangeParameterLift_point c a b w _ _
  · rw [MonObj.comp_mul, lineInterchangeParameterLift_g1, lineInterchangeParameterLift_g2, hcb.1]
    exact hby.2.2
  · rw [MonObj.comp_mul, lineInterchangeParameterLift_x1, lineInterchangeParameterLift_x2, hcb.2.2, hax]
    exact hby.1

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameterFactors.Construction
