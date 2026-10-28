import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Action
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Markings
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Construction

/-! # Modeled Abelian -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledAbelian.Lifts

noncomputable section

/-! Construct the quotient of the actual modeled relative subgroup.
Its abelian variety, complementary map, integral action and ordered
marking are outputs of the proved quotient theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (P : Over S)
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model) (n : ℕ)

structure ModeledAbelianQuotient where
  target : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g P.left
  isogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) target
  complement : target.scheme ⟶ (A.pullback P.hom).scheme
  etale : Etale isogeny.hom.left
  complementGroup : IsMonHom complement
  projection_complement : isogeny.hom ≫ complement = (𝟙 (A.pullback P.hom).scheme) ^ n
  complement_projection : complement ≫ isogeny.hom = (𝟙 target.scheme) ^ n
  kernel : ∀ (T : Over P.left) (a : T ⟶ (A.pullback P.hom).scheme),
    a ≫ isogeny.hom = 1 ↔ ∃! h : T ⟶ (AbelianScheme.IsogenyQuotient.Subgroup.Construction.subgroupGroupScheme F R).X,
      h ≫ AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion A P F R = a
  universal : AbelianScheme.IsogenyQuotient.Descent.Construction.QuotientUniversalProperty (AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion A P F R) isogeny.hom

attribute [instance] ModeledAbelianQuotient.etale ModeledAbelianQuotient.complementGroup

def constructModeledAbelianQuotient
    {k : Type u} [Field k] [CharZero k] (base : S ⟶ Spec (.of k)) (hn : 0 < n)
    (hk : F.KilledBy n) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) : ModeledAbelianQuotient A P F R n :=
  Classical.choice (by
    obtain ⟨B, f, c, he, hc, hfc, hcf, hkernel, hquotient⟩ :=
      AbelianScheme.IsogenyQuotient.Intrinsic.RelativeQuotient.Construction.native_relative_quotient_from_TorsionQuotient_FiniteDescent A P F R n hk
        (AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) base n hn hTorsionQuotient).2 FiniteDescent.Lifts.verified_FiniteDescentInput
    exact ⟨⟨B, f, c, he, hc, hfc, hcf, hkernel, hquotient⟩⟩)

variable {A P F R n} (Q : ModeledAbelianQuotient A P F R n)

/-- Every coefficient action descends from its proved kernel stability. -/
def ModeledAbelianQuotient.action {O : Type v} [CommRing O]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (hstable : ∀ a, AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable F (ρ.map a)) :
    AbelianModuli.ReferenceFamily.ActionData.IntegralAction O Q.target :=
  (AbelianScheme.IsogenyQuotient.Intrinsic.Action.Construction.native_quotient_integral_action A P F R Q.target Q.isogeny Q.kernel Q.universal ρ hstable).choose

theorem ModeledAbelianQuotient.action_projection {O : Type v} [CommRing O]
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (hstable : ∀ a, AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable F (ρ.map a)) (a : O) :
    Q.isogeny.hom ≫ (Q.action ρ hstable).map a = (ρ.pullback P.hom).map a ≫ Q.isogeny.hom :=
  (AbelianScheme.IsogenyQuotient.Intrinsic.Action.Construction.native_quotient_integral_action A P F R Q.target Q.isogeny Q.kernel Q.universal ρ hstable).choose_spec.1 a

def ModeledAbelianQuotient.level (N : ℕ) (hcop : n.Coprime N)
    (level : (A.pullback P.hom).FullLevel N) : Q.target.FullLevel N :=
  AbelianScheme.IsogenyQuotient.Markings.Construction.transportFullLevel (A.pullback P.hom) Q.target Q.isogeny.hom Q.complement n N hcop
    Q.projection_complement Q.complement_projection level

theorem ModeledAbelianQuotient.level_projection (N : ℕ) (hcop : n.Coprime N)
    (level : (A.pullback P.hom).FullLevel N) (T : Over P.left)
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    ((Q.level N hcop level).hom.app (.op T) c).val =
      (level.hom.app (.op T) c).val ≫ Q.isogeny.hom :=
  AbelianScheme.IsogenyQuotient.Markings.Construction.transportFullLevel_apply (A.pullback P.hom) Q.target Q.isogeny.hom Q.complement n N hcop
    Q.projection_complement Q.complement_projection level T c

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledAbelian.Lifts
