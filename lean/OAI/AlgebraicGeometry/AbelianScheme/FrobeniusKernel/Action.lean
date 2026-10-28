import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientActionBase
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FrobeniusLevel
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed

/-! # Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Action.Construction

noncomputable section

/-!
The isogeny underlying the Frobenius quotient carries exactly the pulled
back integral action and full marking. The action comparison is derived
from naturality and uniqueness of fpqc descent.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {S : Scheme.{u}} {g : ℕ}
variable (q : ℕ) (hq : q.Prime) (hS : (q : Γ(S, ⊤)) = 0)
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

/-- Homomorphisms supplies the finite flat relative Frobenius map; its target is the
native base change of the original abelian scheme. -/
def frobeniusIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A
    (A.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq S hS)) where
  hom := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hS A.scheme
  preservesGroup := Picard.Homomorphisms.Group.Construction.relativeFrobenius_isMonHom q hq hS A.scheme
  finite := (Picard.Homomorphisms.Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient q hq hS A.scheme).1.1
  flat := (Picard.Homomorphisms.Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient q hq hS A.scheme).1.2.1
  surjective := (Picard.Homomorphisms.Quotient.Construction.relativeFrobenius_finiteLocallyFree_quotient q hq hS A.scheme).2.1

variable {A} {R : Type v} [CommRing R]

theorem relativeFrobenius_action_intertwines (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (r : R) :
    ρ.map r ≫ (frobeniusIsogeny q hq hS A).hom =
      (frobeniusIsogeny q hq hS A).hom ≫
        (ρ.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq S hS)).map r :=
  (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q hq hS).naturality (ρ.map r)

/-- Kernel stability follows from relative Frobenius naturality on the
actual action, including on nonreduced tests. -/
theorem frobenius_actionStableKernel (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) :
    QuotientActionBase.Construction.ActionStableKernel ρ (frobeniusIsogeny q hq hS A) := by
  intro r T x hx
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => x ≫ f) (relativeFrobenius_action_intertwines q hq hS ρ r)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ (ρ.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq S hS)).map r) hx).trans
          (MonObj.one_comp _))))

/-- The action constructed by quotient descent equals the action on the
Frobenius twist, for every coefficient. -/
theorem frobenius_quotientAction_eq_pullback (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (r : R) :
    (QuotientActionBase.Construction.quotientAction ρ (frobeniusIsogeny q hq hS A)
      (frobenius_actionStableKernel q hq hS ρ)).map r =
        (ρ.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq S hS)).map r :=
  (QuotientActionBase.Construction.quotientAction_unique ρ (frobeniusIsogeny q hq hS A)
    (frobenius_actionStableKernel q hq hS ρ)
    (ρ.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq S hS))
    (fun r => (relativeFrobenius_action_intertwines q hq hS ρ r).symm) r).symm

/-- A prescribed subgroup killed by n gives the killed-kernel input needed
to transport prime-to-n level. This again quantifies over every test scheme. -/
theorem prescribedKernel_killedBy {B H : Over S} [GrpObj B]
    (F : A.scheme ⟶ B) (i : H ⟶ A.scheme) (h : Prescribed.Construction.PrescribedKernel F i)
    (n : ℕ) (hi : i ^ n = 1) (T : Over S) (x : T ⟶ A.scheme)
    (hx : x ≫ F = 1) : x ^ n = 1 := by
  obtain ⟨y, hy, _⟩ := (h T x).mp hx
  have ht : (y ≫ i) ^ n = 1 := by
    rw [← MonObj.comp_pow, hi, MonObj.comp_one]
  exact (congrArg (fun a => a ^ n) hy.symm).trans ht

/-- The descended full marking is equal to the Frobenius-pulled-back
marking as a natural isomorphism, including its actual chosen basis. -/
theorem frobenius_quotientLevel_eq_pullback {n N : ℕ}
    (hnN : Nat.Coprime n N)
    (hkernel : ∀ (T : Over S) (x : T ⟶ A.scheme),
      x ≫ (frobeniusIsogeny q hq hS A).hom = 1 → x ^ n = 1)
    (level : A.FullLevel N) :
    Power.Construction.quotientLevel (frobeniusIsogeny q hq hS A) hnN hkernel level =
      level.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq S hS) := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro c
  apply Subtype.ext
  exact (Power.Construction.quotientLevel_transports (frobeniusIsogeny q hq hS A) hnN hkernel level T c).trans
    (FrobeniusLevel.Construction.relativeFrobenius_transports_level q hq hS level T.unop c).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Action.Construction
