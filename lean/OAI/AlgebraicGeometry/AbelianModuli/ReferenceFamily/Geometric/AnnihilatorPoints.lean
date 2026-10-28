import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleSubgroupContainment
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SheafPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplicative
import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced

/-! # Annihilator Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.AnnihilatorPoints

noncomputable section

/-! For the actual finite etale subgroup model over an algebraically
closed field, ordinary field points detect the full relative
annihilator condition. The proof recovers a scheme-map equality
before returning to arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplicative.Construction

theorem geometric_annihilator_membership
    {k : Type} [Field k] [IsAlgClosed k]
    {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
    [IsFinite A.hom] [Etale A.hom]
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := A) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A (Over.mk (𝟙 (Spec (.of k))))) (R : F.Model)
    (y : Over.mk (𝟙 (Spec (.of k))) ⟶ A) :
    y ∈ (e.relativeAnnihilator F).points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _) ↔
      ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ A,
        x ∈ F.points (Over.mk (𝟙 (Spec (.of k)))) (𝟙 _) → e.pairValue x y = 1 := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  constructor
  · intro h x hx
    have h' := h T (𝟙 T) x (by simpa only [Category.id_comp] using hx)
    simpa only [Category.id_comp] using h'
  · intro h
    have hp : R.toBase.left = R.carrier.hom := by
      have h : R.toBase.left ≫ 𝟙 _ = R.carrier.hom := R.toBase.w
      exact (Category.comp_id _).symm.trans h
    let : Etale R.carrier.hom := hp ▸ AbelianScheme.TorsionQuotient.EtaleSubgroup.EtaleSubgroupModels.etale R
    let : IsReduced R.carrier.left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field R.carrier.hom
    let W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X
    let : Smooth W.hom := AbelianScheme.IsogenyQuotient.Multiplicative.Construction.multiplicativeGroupOver_smooth _
    let : IsSeparated W.hom := AbelianScheme.IsogenyQuotient.Multiplicative.Construction.multiplicativeGroupOver_separated _
    have he : e.pairValue R.toGroup (R.toBase ≫ y) = 1 := by
      apply Albanese.Construction.ClosedPoints.hom_ext_of_points R.carrier W
      intro z
      have hz : z ≫ R.toBase = 𝟙 T := by
        apply Over.OverMorphism.ext
        change (z ≫ R.toBase).left = 𝟙 _
        have h : (z ≫ R.toBase).left ≫ 𝟙 _ = 𝟙 _ := (z ≫ R.toBase).w
        exact (Category.comp_id _).symm.trans h
      have hx : z ≫ R.toGroup ∈ F.points T (𝟙 T) :=
        (R.points_iff T (𝟙 T) (z ≫ R.toGroup)).mpr ⟨z, hz, rfl⟩
      have hv := e.pairValue_natural z R.toGroup (R.toBase ≫ y)
      rw [← Category.assoc, hz, Category.id_comp] at hv
      exact hv.symm.trans ((h (z ≫ R.toGroup) hx).trans (MonObj.comp_one z).symm)
    intro U b x hx
    have hx' : x ∈ F.points U b := by simpa only [Category.comp_id] using hx
    obtain ⟨r, hrb, hrx⟩ := (R.points_iff U b x).mp hx'
    calc
      e.pairValue x (b ≫ y) = e.pairValue (r ≫ R.toGroup) (r ≫ (R.toBase ≫ y)) := by
        rw [← Category.assoc, hrb, hrx]
      _ = r ≫ e.pairValue R.toGroup (R.toBase ≫ y) := e.pairValue_natural r R.toGroup (R.toBase ≫ y)
      _ = 1 := by rw [he, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.AnnihilatorPoints
