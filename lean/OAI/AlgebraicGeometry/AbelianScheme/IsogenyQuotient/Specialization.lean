import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Markings
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Specialization.Construction

noncomputable section

/-!
An independently constructed quotient with the original specialized
kernel is canonically the actual base change of the universal quotient.
The comparison preserves descended actions and ordered full markings.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

universe u v

variable {S : Scheme.{u}} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) (P : Over S)
  (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model)
  {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d P.left}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) B)
  (hker : ∀ (U : Over P.left) (x : U ⟶ (A.pullback P.hom).scheme),
    x ≫ f.hom = 1 ↔ ∃! h : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
      h ≫ Intrinsic.Stability.Construction.nativeSubgroupInclusion A P F R = x)
  {T : Scheme.{u}} (b : T ⟶ P.left) {C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d T}
  (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny ((A.pullback P.hom).pullback b) C)
  (hr : ∀ (U : Over T) (x : U ⟶ ((A.pullback P.hom).pullback b).scheme),
    x ≫ r.hom = 1 ↔
      A.baseChangePointsMulEquiv P.hom ((Over.map b).obj U)
        ((A.pullback P.hom).baseChangePointsMulEquiv b U x) ∈
      F.points ((Over.map P.hom).obj ((Over.map b).obj U))
        (Relative.ParameterBaseChange.Construction.parameterBasePoint P ((Over.map b).obj U)))

include hker hr in
theorem nativeQuotient_pullback_sameKernel : Isogenies.NeighborCounting.QuotientComparison.SameKernel (f.pullback b) r := by
  intro U x
  exact (Intrinsic.KernelPoints.Construction.nativeQuotient_pullback_kernel_membership A P F R f hker b U x).trans (hr U x).symm

def nativeQuotientSpecializationIso : (B.pullback b).scheme ≅ C.scheme :=
  Isogenies.NeighborCounting.QuotientComparison.quotientIso (f.pullback b) r (nativeQuotient_pullback_sameKernel A P F R f hker b r hr)

instance nativeQuotientSpecializationIso_isMonHom :
    IsMonHom (nativeQuotientSpecializationIso A P F R f hker b r hr).hom :=
  Isogenies.NeighborCounting.QuotientComparison.quotientIso_isMonHom _ _ _

theorem nativeQuotientSpecializationIso_projection :
    (f.pullback b).hom ≫ (nativeQuotientSpecializationIso A P F R f hker b r hr).hom = r.hom :=
  Isogenies.NeighborCounting.QuotientComparison.quotientIso_projection _ _ _

theorem nativeQuotientSpecializationIso_unique
    (e : (B.pullback b).scheme ≅ C.scheme)
    (he : (f.pullback b).hom ≫ e.hom = r.hom) :
    e = nativeQuotientSpecializationIso A P F R f hker b r hr := by
  have : EffectiveEpi (f.pullback b).hom := Picard.PoincareBundle.Epi.Construction.effectiveEpi_over_of_fpqc (f.pullback b).hom
  apply Iso.ext
  apply (cancel_epi (f.pullback b).hom).mp
  exact he.trans (nativeQuotientSpecializationIso_projection A P F R f hker b r hr).symm

theorem nativeQuotientSpecializationIso_action
    {O : Type v} [CommRing O]
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O ((A.pullback P.hom).pullback b))
    (α : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O (B.pullback b)) (β : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O C)
    (hα : ∀ a, (f.pullback b).hom ≫ α.map a = σ.map a ≫ (f.pullback b).hom)
    (hβ : ∀ a, r.hom ≫ β.map a = σ.map a ≫ r.hom) (a : O) :
    α.map a ≫ (nativeQuotientSpecializationIso A P F R f hker b r hr).hom =
      (nativeQuotientSpecializationIso A P F R f hker b r hr).hom ≫ β.map a := by
  have : EffectiveEpi (f.pullback b).hom := Picard.PoincareBundle.Epi.Construction.effectiveEpi_over_of_fpqc (f.pullback b).hom
  apply (cancel_epi (f.pullback b).hom).mp
  rw [← Category.assoc, hα, Category.assoc, nativeQuotientSpecializationIso_projection,
    ← Category.assoc, nativeQuotientSpecializationIso_projection, hβ]

theorem nativeQuotientSpecializationIso_marking
    (back : (B.pullback b).scheme ⟶ ((A.pullback P.hom).pullback b).scheme) [IsMonHom back]
    (back' : C.scheme ⟶ ((A.pullback P.hom).pullback b).scheme) [IsMonHom back']
    (n N : ℕ) (hcop : Nat.Coprime n N)
    (hfb : (f.pullback b).hom ≫ back = (𝟙 ((A.pullback P.hom).pullback b).scheme) ^ n)
    (hbf : back ≫ (f.pullback b).hom = (𝟙 (B.pullback b).scheme) ^ n)
    (hrb : r.hom ≫ back' = (𝟙 ((A.pullback P.hom).pullback b).scheme) ^ n)
    (hbr : back' ≫ r.hom = (𝟙 C.scheme) ^ n)
    (level : ((A.pullback P.hom).pullback b).FullLevel N)
    (U : Over T) (c : LocallyConstant U.left (Multiplicative (Fin (2 * d) → ZMod N))) :
    ((Markings.Construction.transportFullLevel _ _ (f.pullback b).hom back n N hcop hfb hbf level).hom.app (.op U) c).val ≫
        (nativeQuotientSpecializationIso A P F R f hker b r hr).hom =
      ((Markings.Construction.transportFullLevel _ _ r.hom back' n N hcop hrb hbr level).hom.app (.op U) c).val := by
  rw [Markings.Construction.transportFullLevel_apply, Markings.Construction.transportFullLevel_apply, Category.assoc,
    nativeQuotientSpecializationIso_projection]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Specialization.Construction
