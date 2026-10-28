import OAI.NumberTheory.PadicHodge.IntegralComparison.TorsionSchemeCharacter
import OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction

/-! # Torsion Point Character -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TorsionPointCharacter

noncomputable section

/-! The overlap cocycle is additive on actual torsion points. This gives
the finite-level pairing used in the H¹/dual-Tate comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

open OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

local notation "N" => (ℓ ^ n)
local notation "T" => OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A N
local notation "m" => ((𝟙 A : A ⟶ A) ^ N)

def torsionPoint (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) : 𝟙_ (Over (Spec (.of k))) ⟶ T :=
  AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift N t.val t.property

def translation (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) : A ⟶ A :=
  𝟙 A * (toUnit A ≫ t.val)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem translation_multiplication (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    translation ℓ n A t ≫ m = m := by
  change (𝟙 A * (toUnit A ≫ t.val)) ≫ (𝟙 A) ^ N = (𝟙 A) ^ N
  rw [MonObj.comp_pow, Category.comp_id, mul_pow]
  have ht : (toUnit A ≫ t.val) ^ N = 1 := by
    rw [← MonObj.comp_pow, show t.val ^ N = 1 from t.property, MonObj.comp_one]
  rw [ht, _root_.mul_one]

def pair (f : A ⟶ A) (hf : f ≫ m = m) (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    MultiplicationCoverCharacter.cover ℓ n A hℓ ⟶ MultiplicationCoverCharacter.overlap ℓ n A hℓ :=
  MorphismProperty.Over.homMk
    ((lift f (toUnit A ≫ torsionPoint ℓ n A t)).left ≫
      (MultiplicationKernelPair.schemeEquiv A N).hom) (by
        change ((lift f (toUnit A ≫ torsionPoint ℓ n A t)).left ≫
          (MultiplicationKernelPair.schemeEquiv A N).hom) ≫
            (pullback.fst (m).left (m).left ≫ (m).left) = (m).left
        rw [Category.assoc, MultiplicationKernelPair.schemeEquiv_hom_fst_assoc]
        have he : lift f (toUnit A ≫ torsionPoint ℓ n A t) ≫ fst A T ≫ m = m := by
          rw [← Category.assoc, lift_fst, hf]
        exact congrArg Over.Hom.left he)

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc] theorem pair_fst (f : A ⟶ A) (hf : f ≫ m = m)
    (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    (pair ℓ n A hℓ f hf t).left ≫ (MultiplicationCoverCharacter.first ℓ n A hℓ).left = f.left := by
  change ((lift f (toUnit A ≫ torsionPoint ℓ n A t)).left ≫
    (MultiplicationKernelPair.schemeEquiv A N).hom) ≫ pullback.fst (m).left (m).left = _
  rw [Category.assoc, MultiplicationKernelPair.schemeEquiv_hom_fst]
  exact congrArg Over.Hom.left (lift_fst f (toUnit A ≫ torsionPoint ℓ n A t))

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
@[reassoc] theorem pair_snd (f : A ⟶ A) (hf : f ≫ m = m)
    (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    (pair ℓ n A hℓ f hf t).left ≫ (MultiplicationCoverCharacter.second ℓ n A hℓ).left =
      (f * (toUnit A ≫ t.val)).left := by
  change ((lift f (toUnit A ≫ torsionPoint ℓ n A t)).left ≫
    (MultiplicationKernelPair.schemeEquiv A N).hom) ≫ pullback.snd (m).left (m).left = _
  rw [Category.assoc, MultiplicationKernelPair.schemeEquiv_hom_snd]
  have he : lift f (toUnit A ≫ torsionPoint ℓ n A t) ≫
      ((fst A T) * (snd A T ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N)) = f * (toUnit A ≫ t.val) := by
    simp only [MonObj.comp_mul, lift_fst, lift_snd_assoc, Category.assoc,
      torsionPoint, AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι]
  exact congrArg Over.Hom.left he

def value (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
    (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) : ZMod N :=
  TorsionSchemeCharacter.character ℓ n A hℓ x
    ((torsionPoint ℓ n A t).left (IsLocalRing.closedPoint k))

theorem pair_value (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
    (f : A ⟶ A) (hf : f ≫ m = m) (t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) (z : A.left) :
    ULift.down (α := C(A.left, ZMod N))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map (pair ℓ n A hℓ f hf t).op
        (MultiplicationCoverCharacter.character ℓ n A hℓ x)) z =
        value ℓ n A hℓ x t := by
  change MultiplicationCoverCharacter.productCharacter ℓ n A hℓ x ((lift f (toUnit A ≫ torsionPoint ℓ n A t)).left z) = _
  rw [TorsionSchemeCharacter.productCharacter_value]
  have he := congrArg Over.Hom.left (lift_snd f (toUnit A ≫ torsionPoint ℓ n A t))
  have hz := congrArg (fun g : A.left ⟶ (T).left => g z) he
  change (snd A T).left ((lift f (toUnit A ≫ torsionPoint ℓ n A t)).left z) =
    (torsionPoint ℓ n A t).left ((toUnit A).left z) at hz
  rw [hz, show (toUnit A).left z = IsLocalRing.closedPoint k from
    Subsingleton.elim (α := Spec (.of k)) _ _]
  rfl

theorem value_mul (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
    (t u : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) :
    value ℓ n A hℓ x (t * u) = value ℓ n A hℓ x t + value ℓ n A hℓ x u := by
  let U := MultiplicationCoverCharacter.cover ℓ n A hℓ
  let D := MultiplicationCoverCharacter.overlap ℓ n A hℓ
  let a := MultiplicationCoverCharacter.first ℓ n A hℓ
  let b := MultiplicationCoverCharacter.second ℓ n A hℓ
  let p := pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) t
  let q := pair ℓ n A hℓ (translation ℓ n A t) (translation_multiplication ℓ n A t) u
  let r := pair ℓ n A hℓ (𝟙 A) (Category.id_comp m) (t * u)
  have hpa : p ≫ a = r ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact (pair_fst ℓ n A hℓ _ _ _).trans (pair_fst ℓ n A hℓ _ _ _).symm
  have hpb : p ≫ b = q ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact (pair_snd ℓ n A hℓ _ _ _).trans (pair_fst ℓ n A hℓ _ _ _).symm
  have hqb : q ≫ b = r ≫ b := by
    apply MorphismProperty.Over.Hom.ext
    change q.left ≫ b.left = r.left ≫ b.left
    rw [pair_snd, pair_snd]
    apply congrArg Over.Hom.left
    change (𝟙 A * (toUnit A ≫ t.val)) * (toUnit A ≫ u.val) =
      𝟙 A * (toUnit A ≫ (t.val * u.val))
    rw [MonObj.comp_mul, _root_.mul_assoc]
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let : PreconnectedSpace U.left := inferInstanceAs (PreconnectedSpace A.left)
  have he := Finite.CoverCharacter.character_cocycle ℓ n U D a b
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A)
    x U p q r hpa hpb hqb
  let z : A.left := Classical.choice inferInstance
  have hz := congrArg (fun s : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.obj (op U) =>
    ULift.down (α := C(A.left, ZMod N)) s z) he
  change ULift.down (α := C(A.left, ZMod N))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map p.op
        (MultiplicationCoverCharacter.character ℓ n A hℓ x)) z +
    ULift.down (α := C(A.left, ZMod N))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map q.op
        (MultiplicationCoverCharacter.character ℓ n A hℓ x)) z =
    ULift.down (α := C(A.left, ZMod N))
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.map r.op
        (MultiplicationCoverCharacter.character ℓ n A hℓ x)) z at hz
  rw [pair_value, pair_value, pair_value] at hz
  exact hz.symm

theorem value_one (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    value ℓ n A hℓ x 1 = 0 := by
  have h := value_mul ℓ n A hℓ x 1 1
  rw [_root_.one_mul] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

def pointCharacter (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1) :
    Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N where
  toFun t := value ℓ n A hℓ x t.toMul
  map_zero' := value_one ℓ n A hℓ x
  map_add' t u := value_mul ℓ n A hℓ x t.toMul u.toMul

def character : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1 →+
    (Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N) where
  toFun := pointCharacter ℓ n A hℓ
  map_zero' := by
    apply AddMonoidHom.ext
    intro t
    change TorsionSchemeCharacter.character ℓ n A hℓ 0 _ = 0
    rw [map_zero]
    rfl
  map_add' x y := by
    apply AddMonoidHom.ext
    intro t
    change TorsionSchemeCharacter.character ℓ n A hℓ (x + y) _ =
      TorsionSchemeCharacter.character ℓ n A hℓ x _ +
        TorsionSchemeCharacter.character ℓ n A hℓ y _
    rw [map_add]
    rfl

theorem character_injective : Function.Injective (character ℓ n A hℓ) := by
  intro x y hxy
  apply TorsionSchemeCharacter.character_injective ℓ n A hℓ
  let : IsFinite (T).hom := (AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.torsionScheme_finite_etale A N
    (by rw [Nat.cast_pow]; exact pow_ne_zero n hℓ)).1
  let : JacobsonSpace (T).left := LocallyOfFiniteType.jacobsonSpace (T).hom
  let c := TorsionSchemeCharacter.character ℓ n A hℓ x
  let d := TorsionSchemeCharacter.character ℓ n A hℓ y
  apply DFunLike.ext'
  apply c.continuous.ext_on (show Dense (closedPoints (T).left) by
    rw [dense_iff_closure_eq, closure_closedPoints]) d.continuous
  intro z hz
  let s : 𝟙_ (Over (Spec (.of k))) ⟶ T := Over.homMk
    (pointOfClosedPoint (T).hom z hz) (pointOfClosedPoint_comp (T).hom z hz)
  let t : AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N := ⟨s ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N,
    (AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.factors_through_torsion_iff N (s ≫ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionι A N)).mp ⟨s, rfl⟩⟩
  have ht : torsionPoint ℓ n A t = s := by
    apply equalizer.hom_ext
    exact AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι N t.val t.property
  have he := congrArg
    (fun f : Additive (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A N) →+ ZMod N => f (Additive.ofMul t)) hxy
  change value ℓ n A hℓ x t = value ℓ n A hℓ y t at he
  unfold value at he
  rw [ht] at he
  change c (pointOfClosedPoint (T).hom z hz (IsLocalRing.closedPoint k)) =
    d (pointOfClosedPoint (T).hom z hz (IsLocalRing.closedPoint k)) at he
  simpa only [pointOfClosedPoint_apply] using he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TorsionPointCharacter
