import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualNumberReduction

/-! # Lie Points -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LiePoints

noncomputable section

/-! An actual module of infinitesimal stalk lifts parametrizes the
identity-based dual-number points of a group scheme over every field. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace AlgebraicLie

variable {k : Type} [Field k]

abbrev Space (A : Over (Spec (.of k))) [MonObj A] :=
  AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A

instance spaceModule (A : Over (Spec (.of k))) [MonObj A] : Module k (Space A) :=
  Module.compHom (Space A) (algebraMap k (DualNumber k))

def point (A : Over (Spec (.of k))) [MonObj A] (v : Space A) : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A :=
  AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A v

theorem point_injective (A : Over (Spec (.of k))) [MonObj A] : Function.Injective (point A) :=
  AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_injective (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A

theorem point_zero (A : Over (Spec (.of k))) [MonObj A] : point A 0 = 1 :=
  AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_zero (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A

theorem point_origin (A : Over (Spec (.of k))) [MonObj A] (v : Space A) :
    AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ point A v = 1 := by
  have h := AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.point_reduction (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) A).hom v.val
  have h' := (DualNumberReduction.AlgebraicLie.quotient_reduction_eq_iff k _ _).mp h
  apply Over.OverMorphism.ext
  exact h'.trans (congrArg Over.Hom.left (MonObj.comp_one (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k)))

theorem mem_relative_of_point_over (A : Over (Spec (.of k))) [MonObj A]
    (v : AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.Space (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A)
    (hv : AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A v ≫
      A.hom = (DualNumberReduction.AlgebraicLie.dualBase k)) :
    v ∈ AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A := by
  apply AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_injective (DualNumberReduction.AlgebraicLie.dualBase k)
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (𝟙_ (Over (Spec (.of k))))
  rw [AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent, AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_zero]
  exact hv

theorem exists_point (A : Over (Spec (.of k))) [MonObj A]
    (f : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A) (hf : AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ f = 1) :
    ∃ v : Space A, point A v = f := by
  have he : (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k).left ≫ f.left =
      (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k).left ≫ (1 : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A).left :=
    congrArg Over.Hom.left (hf.trans (MonObj.comp_one (AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k)).symm)
  have heq := (DualNumberReduction.AlgebraicLie.quotient_reduction_eq_iff k f.left
    (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) A).hom).mpr he
  obtain ⟨v, hv⟩ := AbelianScheme.TorsionQuotient.PointedTangentAt.PointedTangent.exists_point (C := .of (DualNumber k)) (X := A.left)
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) A).hom f.left heq
  have hker : v ∈ AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative (DualNumberReduction.AlgebraicLie.dualBase k)
      (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A :=
    mem_relative_of_point_over A v ((congrArg (fun q => q ≫ A.hom) hv).trans f.w)
  exact ⟨⟨v, hker⟩, Over.OverMorphism.ext hv⟩

def pointsEquiv (A : Over (Spec (.of k))) [MonObj A] :
    Space A ≃ {f : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ A // AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ f = 1} :=
  Equiv.ofBijective (fun v => ⟨point A v, point_origin A v⟩)
    ⟨fun _ _ h => point_injective A (congrArg Subtype.val h), by
      rintro ⟨f, hf⟩
      obtain ⟨v, hv⟩ := exists_point A f hf
      exact ⟨v, Subtype.ext hv⟩⟩

theorem point_add (A : Over (Spec (.of k))) [MonObj A] [IsCommMonObj A] (v w : Space A) :
    point A (v + w) = point A v * point A w :=
  AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint_add (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A v w

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LiePoints
