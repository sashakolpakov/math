import OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionTestPoints
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TestSchemeLift

/-! # Orthogonal Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalBaseChange

noncomputable section

/-! Full scheme-valued self-annihilation is preserved by base change. Every original test over a changed-base parameter is explicitly recovered; geometric points alone are never substituted for scheme tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionTestPoints

variable {S S' : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) (n : ℕ)
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)

/-- The full annihilator subfunctor equals the represented kernel inside n-torsion. -/
def SelfAnnihilating (V : ∀ T : Over S, TorsionTestPoints.Point A n T → TorsionTestPoints.Point A n T → Γ(T.left, ⊤)ˣ) : Prop :=
  ∀ (T : Over S) (y : TorsionTestPoints.Point A n T),
    (∀ (U : Over S) (a : U ⟶ T) (x : U ⟶ A) (hx : x ≫ f = 1),
      V U ⟨x, hker U x hx⟩ (TorsionTestPoints.restrict a y) = 1) ↔ y.val ≫ f = 1

include hker in
/-- Kernel containment is preserved on the complete point functor. -/
theorem containment (s : S' ⟶ S) (T : Over S') (x : T ⟶ (Over.pullback s).obj A)
    (hx : x ≫ (Over.pullback s).map f = 1) : x ^ n = 1 := by
  let e := Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsMulEquiv A s T
  have h0 := hker ((Over.map s).obj T) (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T x) ((TorsionTestPoints.kernel_iff s f T x).mp hx)
  apply e.injective
  exact (map_pow e x n).trans (h0.trans (map_one e).symm)

variable (V : ∀ T : Over S, TorsionTestPoints.Point A n T → TorsionTestPoints.Point A n T → Γ(T.left, ⊤)ˣ)
  (hV : ∀ {T U : Over S} (a : U ⟶ T) (x y : TorsionTestPoints.Point A n T),
    V U (TorsionTestPoints.restrict a x) (TorsionTestPoints.restrict a y) = Units.map a.left.appTop.hom (V T x y))
  (s : S' ⟶ S)
  (W : ∀ T : Over S', TorsionTestPoints.Point ((Over.pullback s).obj A) n T → TorsionTestPoints.Point ((Over.pullback s).obj A) n T → Γ(T.left, ⊤)ˣ)
  (hW : ∀ (T : Over S') (x y : TorsionTestPoints.Point ((Over.pullback s).obj A) n T),
    W T x y = V ((Over.map s).obj T) (TorsionTestPoints.pullbackEquiv s A n T x) (TorsionTestPoints.pullbackEquiv s A n T y))

include hV hW

/-- Naturality and the proved pairing comparison transport full self-annihilation through arbitrary base change. -/
theorem selfAnnihilating (h : SelfAnnihilating f n hker V) :
    SelfAnnihilating ((Over.pullback s).map f) n (containment f n hker s) W := by
  intro T y
  constructor
  · intro hy
    apply (TorsionTestPoints.kernel_iff s f T y.val).mpr
    apply (h ((Over.map s).obj T) (TorsionTestPoints.pullbackEquiv s A n T y)).mp
    intro U a x hx
    let U' := TestSchemeLift.object s T U a
    let e := TestSchemeLift.iso s T U a
    let b := TestSchemeLift.map s T U a
    let x0 : TorsionTestPoints.Point A n U := ⟨x, hker U x hx⟩
    let xp := (TorsionTestPoints.pullbackEquiv s A n U').symm (TorsionTestPoints.restrict e.hom x0)
    have hxp : TorsionTestPoints.pullbackEquiv s A n U' xp = TorsionTestPoints.restrict e.hom x0 :=
      (TorsionTestPoints.pullbackEquiv s A n U').apply_symm_apply _
    have hxpf : xp.val ≫ (Over.pullback s).map f = 1 := by
      apply (TorsionTestPoints.kernel_iff s f U' xp.val).mpr
      have hp : Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s U' xp.val = e.hom ≫ x := congrArg Subtype.val hxp
      exact (congrArg (fun z => z ≫ f) hp).trans
        ((Category.assoc _ _ _).trans ((congrArg (fun z => e.hom ≫ z) hx).trans (MonObj.comp_one e.hom)))
    have hyp : TorsionTestPoints.pullbackEquiv s A n U' (TorsionTestPoints.restrict b y) =
        TorsionTestPoints.restrict e.hom (TorsionTestPoints.restrict a (TorsionTestPoints.pullbackEquiv s A n T y)) :=
      (TorsionTestPoints.pullback_restrict s A n b y).trans
        ((congrArg (fun q => TorsionTestPoints.restrict q (TorsionTestPoints.pullbackEquiv s A n T y)) (TestSchemeLift.map_eq s T U a)).trans
          (TorsionTestPoints.restrict_comp a e.hom (TorsionTestPoints.pullbackEquiv s A n T y)).symm)
    have hw : W U' xp (TorsionTestPoints.restrict b y) = 1 := hy U' b xp.val hxpf
    have hv : V ((Over.map s).obj U') (TorsionTestPoints.restrict e.hom x0)
        (TorsionTestPoints.restrict e.hom (TorsionTestPoints.restrict a (TorsionTestPoints.pullbackEquiv s A n T y))) = 1 :=
      (congrArg₂ (V ((Over.map s).obj U')) hxp hyp).symm.trans ((hW U' xp (TorsionTestPoints.restrict b y)).symm.trans hw)
    have hn := hV e.hom x0 (TorsionTestPoints.restrict a (TorsionTestPoints.pullbackEquiv s A n T y))
    have hid : Units.map e.hom.left.appTop.hom.toMonoidHom (V U x0 (TorsionTestPoints.restrict a (TorsionTestPoints.pullbackEquiv s A n T y))) =
        V U x0 (TorsionTestPoints.restrict a (TorsionTestPoints.pullbackEquiv s A n T y)) := by
      change Units.map (Scheme.Hom.appTop (𝟙 U.left)).hom.toMonoidHom _ = _
      simp
    exact hid.symm.trans (hn.symm.trans hv)
  · intro hy
    have hy0 : (TorsionTestPoints.pullbackEquiv s A n T y).val ≫ f = 1 := (TorsionTestPoints.kernel_iff s f T y.val).mp hy
    have hyall := (h ((Over.map s).obj T) (TorsionTestPoints.pullbackEquiv s A n T y)).mpr hy0
    intro U b x hx
    let xp : TorsionTestPoints.Point ((Over.pullback s).obj A) n U := ⟨x, containment f n hker s U x hx⟩
    let x0 := TorsionTestPoints.pullbackEquiv s A n U xp
    have hx0 : x0.val ≫ f = 1 := (TorsionTestPoints.kernel_iff s f U x).mp hx
    have hv : V ((Over.map s).obj U) x0 (TorsionTestPoints.restrict ((Over.map s).map b) (TorsionTestPoints.pullbackEquiv s A n T y)) = 1 :=
      hyall ((Over.map s).obj U) ((Over.map s).map b) x0.val hx0
    exact (hW U xp (TorsionTestPoints.restrict b y)).trans
      ((congrArg (V ((Over.map s).obj U) x0) (TorsionTestPoints.pullback_restrict s A n b y)).trans hv)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalBaseChange
