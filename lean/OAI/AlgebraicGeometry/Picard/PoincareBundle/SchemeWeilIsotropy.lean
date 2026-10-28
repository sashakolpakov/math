import OAI.AlgebraicGeometry.Picard.PoincareBundle.OrthogonalBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentBaseChange

/-! # Scheme Weil Isotropy -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilIsotropy

noncomputable section

/-! Original-field maximal isotropy is equality of full scheme-valued annihilators for the actual Weil pairing. Its geometric base changes are consequences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TorsionTestPoints

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}

section Pairing
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n)

/-- The actual standard Weil pairing on the full represented torsion-point functor. -/
def value (T : Over (Spec (.of k))) (x y : TorsionTestPoints.Point A.scheme n T) : Γ(T.left, ⊤)ˣ :=
  PoincareBundle.Field.WeilPairing.value D ell n hn x.val x.property y.val y.property

/-- Naturality is proved for all test schemes. -/
theorem natural {T U : Over (Spec (.of k))} (f : U ⟶ T) (x y : TorsionTestPoints.Point A.scheme n T) :
    value D ell n hn U (TorsionTestPoints.restrict f x) (TorsionTestPoints.restrict f y) = Units.map f.left.appTop.hom (value D ell n hn T x y) :=
  PoincareBundle.Field.WeilPairing.natural D ell n hn f x.val x.property (TorsionTestPoints.restrict f x).property
    y.val y.property (TorsionTestPoints.restrict f y).property

/-- The pairing itself, not just its geometric points, commutes with field extension. -/
theorem value_baseChange {K : Type} [Field K] (s : Spec (.of K) ⟶ Spec (.of k))
    (T : Over (Spec (.of K))) (x y : TorsionTestPoints.Point (A.pullback s).scheme n T) :
    value (D.pullback s) (ell.pullback s) n hn T x y =
      value D ell n hn ((Over.map s).obj T) (TorsionTestPoints.pullbackEquiv s A.scheme n T x) (TorsionTestPoints.pullbackEquiv s A.scheme n T y) :=
  PoincareBundle.Field.WeilBaseChange.value D ell n hn s T x.val x.property y.val y.property

end Pairing

variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
  (hker : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)

/-- The original full subgroup-scheme annihilator equals the kernel inside A[n]; only the original field occurs in this hypothesis. -/
def SelfAnnihilating : Prop :=
  OrthogonalBaseChange.SelfAnnihilating f.hom n hker (value D ell n hn)

/-- The original full self-annihilation hypothesis implies full self-annihilation after every field extension. -/
theorem baseChange (h : SelfAnnihilating D ell f n hn hker)
    {K : Type} [Field K] (s : Spec (.of K) ⟶ Spec (.of k)) :
    SelfAnnihilating (D.pullback s) (ell.pullback s) (f.pullback s) n hn
      (Kernel.ContainmentBaseChange.contained f n hker s) :=
  OrthogonalBaseChange.selfAnnihilating f.hom n hker (value D ell n hn)
    (natural D ell n hn) s (value (D.pullback s) (ell.pullback s) n hn)
    (value_baseChange D ell n hn s) h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SchemeWeilIsotropy
