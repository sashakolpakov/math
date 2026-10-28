import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Stability
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.RelativeQuotient
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LieRank
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects

/-! # Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Action.Construction

noncomputable section

/-!
The actual integral action on the native ReferenceFamily quotient family. Its kernel
criterion is derived from relative subgroup stability, and its prescribed
geometric Lie ranks are transferred through the proved etale isogeny.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u v

set_option backward.isDefEq.respectTransparency false in
/-- Construct the quotient's integral action on ReferenceFamily's ordinary pullback
family. The stability premise is the all-test property already derived
from the scalar action on the chosen and opposite torsion blocks. -/
theorem native_quotient_integral_action
    {S : Scheme.{u}} {dim : ℕ} {O : Type v} [CommRing O]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim S) (P : Over S)
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model)
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme dim P.left)
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) B)
    (hker : ∀ (T : Over P.left) (a : T ⟶ (A.pullback P.hom).scheme),
      a ≫ f.hom = 1 ↔ ∃! h : T ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
        h ≫ Stability.Construction.nativeSubgroupInclusion A P F R = a)
    (hUP : Descent.Construction.QuotientUniversalProperty (Stability.Construction.nativeSubgroupInclusion A P F R) f.hom)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
    (hstable : ∀ a, Action.Construction.RelativeSubgroupStable F (ρ.map a)) :
    ∃! σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O B,
      ∀ a, f.hom ≫ σ.map a = (ρ.pullback P.hom).map a ≫ f.hom := by
  let i := Stability.Construction.nativeSubgroupInclusion A P F R
  have : IsClosedImmersion i.left := Stability.Construction.nativeSubgroupInclusion_closedImmersion A P F R
  have : Mono i := Over.mono_of_mono_left i
  have hif : i ≫ f.hom = 1 := by
    apply (hker (Subgroup.Construction.subgroupGroupScheme F R).X i).mpr
    refine ⟨𝟙 _, Category.id_comp _, ?_⟩
    intro r hr
    apply (cancel_mono i).mp
    simpa only [Category.id_comp] using hr
  apply PELAction.Construction.quotient_integral_action (A.pullback P.hom) B (ρ.pullback P.hom)
    (Subgroup.Construction.subgroupGroupScheme F R).X i f hif hUP
  intro a
  exact Stability.Construction.native_stable_kernel_equation A P F R (ρ.map a) (hstable a) f.hom hif

/-- The complete ReferenceFamily geometric Lie-signature predicate is preserved by
the equivariant finite-etale quotient; every embedding and base point is
the same one used by the source predicate. -/
theorem prescribed_lie_ranks_after_quotient
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (iota : E →+* K)
    (T : Over (Spec (.of K))) (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) [Etale f.hom.left]
    (hcomm : ∀ a, f.hom ≫ σ.map a = ρ.map a ≫ f.hom)
    (hrank : AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks P iota T A ρ) :
    AbelianModuli.ReferenceFamily.PEL.Objects.HasPrescribedLieRanks P iota T B σ := by
  intro F _ _ j p hp τ
  exact LieRank.Construction.hasLieRank_after_baseChange A B f.hom ρ σ hcomm p
    ((j.comp iota).comp (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)))
    (P.lieRank τ) (hrank F j p hp τ)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Action.Construction
