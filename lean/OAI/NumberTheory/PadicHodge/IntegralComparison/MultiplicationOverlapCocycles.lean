import OAI.NumberTheory.PadicHodge.IntegralComparison.TorsionPointCharacter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.GroupSchemeCharacters
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group

/-! # Multiplication Overlap Cocycles -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationOverlapCocycles

noncomputable section

/-! A character of the actual finite torsion group determines a cocycle
on the actual multiplication-cover overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

local notation "N" => ℓ ^ n
local notation "T" => OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A N
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.cover ℓ n A hℓ
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.overlap ℓ n A hℓ
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.first ℓ n A hℓ
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter.second ℓ n A hℓ
local notation "m" => ((𝟙 A : A ⟶ A) ^ N)

abbrev siteOver (V : A.left.ProEt) : Over (Spec (.of k)) := Over.mk (V.hom ≫ A.hom)

def siteMap {V W : A.left.ProEt} (f : V ⟶ W) : siteOver A V ⟶ siteOver A W :=
  Over.homMk f.left (by
    change f.left ≫ W.hom ≫ A.hom = V.hom ≫ A.hom
    rw [← Category.assoc, MorphismProperty.Over.w])

def toA {V : A.left.ProEt} (f : V ⟶ U) : siteOver A V ⟶ A :=
  Over.homMk f.left (by
    calc
      f.left ≫ A.hom = f.left ≫ (m).left ≫ A.hom :=
        congrArg (fun t => f.left ≫ t) (Over.w m).symm
      _ = V.hom ≫ A.hom := by
        rw [← Category.assoc]
        exact congrArg (fun t => t ≫ A.hom) (MorphismProperty.Over.w f))

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc (attr := simp)] theorem siteMap_toA {V W : A.left.ProEt}
    (f : V ⟶ W) (g : W ⟶ U) :
    siteMap A f ≫ toA ℓ n A hℓ g = toA ℓ n A hℓ (f ≫ g) := rfl

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem toA_pow {V : A.left.ProEt} (f : V ⟶ U) :
    toA ℓ n A hℓ f ^ N = Over.homMk V.hom (by rfl) := by
  have he : toA ℓ n A hℓ f ≫ m = Over.homMk V.hom (by rfl) :=
    Over.OverMorphism.ext (MorphismProperty.Over.w f)
  simpa only [MonObj.comp_pow, Category.comp_id] using he

def difference {V : A.left.ProEt} (f g : V ⟶ U) : siteOver A V ⟶ T :=
  AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift N (toA ℓ n A hℓ g / toA ℓ n A hℓ f) (by
    rw [div_pow, toA_pow, toA_pow, div_self'])

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc (attr := simp)] theorem difference_inclusion {V : A.left.ProEt} (f g : V ⟶ U) :
    difference ℓ n A hℓ f g ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N = toA ℓ n A hℓ g / toA ℓ n A hℓ f :=
  AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc (attr := simp)] theorem difference_comp {V W : A.left.ProEt}
    (p : V ⟶ W) (f g : W ⟶ U) :
    siteMap A p ≫ difference ℓ n A hℓ f g = difference ℓ n A hℓ (p ≫ f) (p ≫ g) := by
  apply equalizer.hom_ext
  change (siteMap A p ≫ difference ℓ n A hℓ f g) ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N =
    difference ℓ n A hℓ (p ≫ f) (p ≫ g) ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N
  simp only [Category.assoc, difference_inclusion, GrpObj.comp_div, siteMap_toA]

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem difference_cocycle {V : A.left.ProEt} (f g h : V ⟶ U) :
    difference ℓ n A hℓ f g * difference ℓ n A hℓ g h = difference ℓ n A hℓ f h := by
  apply equalizer.hom_ext
  change (difference ℓ n A hℓ f g * difference ℓ n A hℓ g h) ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N =
    difference ℓ n A hℓ f h ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N
  rw [MonObj.mul_comp, difference_inclusion, difference_inclusion, difference_inclusion]
  rw [_root_.mul_comm, div_mul_div_cancel]

def pointEquiv : (𝟙_ (Over (Spec (.of k))) ⟶ T) ≃* AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N where
  toEquiv := AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointsEquiv A N _
  map_mul' := AlgebraicGeometry.AbelianScheme.TorsionQuotient.Group.TorsionGroup.pointsEquiv_mul A N _

def schemeFunction (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N) :
    C((T).left, ZMod N) := by
  let : IsFinite (T).hom := (AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.torsionScheme_finite_etale A N
    (by rw [Nat.cast_pow]; exact pow_ne_zero n hℓ)).1
  exact Finite.GroupSchemeCharacters.continuousFunction T
    (fun t => χ (Additive.ofMul (pointEquiv ℓ n A t)))

omit [Fact (Nat.Prime ℓ)] [GeometricallyIntegral A.hom] in
theorem schemeFunction_point (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N)
    (s : 𝟙_ (Over (Spec (.of k))) ⟶ T) :
    schemeFunction ℓ n A hℓ χ (s.left (IsLocalRing.closedPoint k)) =
      χ (Additive.ofMul (pointEquiv ℓ n A s)) := by
  let : IsFinite (T).hom := (AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.torsionScheme_finite_etale A N
    (by rw [Nat.cast_pow]; exact pow_ne_zero n hℓ)).1
  exact Finite.GroupSchemeCharacters.continuousFunction_point T
    (fun t => χ (Additive.ofMul (pointEquiv ℓ n A t))) s

omit [Fact (Nat.Prime ℓ)] [GeometricallyIntegral A.hom] in
theorem schemeFunction_mul (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N)
    {W : Over (Spec (.of k))} (f g : W ⟶ T) (z : W.left) :
    schemeFunction ℓ n A hℓ χ ((f * g).left z) =
      schemeFunction ℓ n A hℓ χ (f.left z) + schemeFunction ℓ n A hℓ χ (g.left z) := by
  let : IsFinite (T).hom := (AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.torsionScheme_finite_etale A N
    (by rw [Nat.cast_pow]; exact pow_ne_zero n hℓ)).1
  exact Finite.GroupSchemeCharacters.pullback_mul T
    (χ.comp (pointEquiv ℓ n A).toMonoidHom.toAdditive) f g z

def cocycle (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N) :
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.obj (op D) :=
  ULift.up ((schemeFunction ℓ n A hℓ χ).comp
    ⟨(difference ℓ n A hℓ a b).left, (difference ℓ n A hℓ a b).left.continuous⟩)

omit [Fact (Nat.Prime ℓ)] [GeometricallyIntegral A.hom] in
theorem cocycle_condition (χ : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N)
    (V : A.left.ProEt) (p q r : V ⟶ D)
    (hpa : p ≫ a = r ≫ a) (hpb : p ≫ b = q ≫ a) (hqb : q ≫ b = r ≫ b) :
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map p.op (cocycle ℓ n A hℓ χ) +
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map q.op (cocycle ℓ n A hℓ χ) =
        (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map r.op (cocycle ℓ n A hℓ χ) := by
  have he : (siteMap A p ≫ difference ℓ n A hℓ a b) *
      (siteMap A q ≫ difference ℓ n A hℓ a b) = siteMap A r ≫ difference ℓ n A hℓ a b := by
    rw [difference_comp, difference_comp, difference_comp, ← hpa, ← hqb, hpb]
    exact difference_cocycle ℓ n A hℓ _ _ _
  apply ULift.ext
  apply ContinuousMap.ext
  intro z
  change schemeFunction ℓ n A hℓ χ ((siteMap A p ≫ difference ℓ n A hℓ a b).left z) +
    schemeFunction ℓ n A hℓ χ ((siteMap A q ≫ difference ℓ n A hℓ a b).left z) =
      schemeFunction ℓ n A hℓ χ ((siteMap A r ≫ difference ℓ n A hℓ a b).left z)
  rw [← schemeFunction_mul, he]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationOverlapCocycles
