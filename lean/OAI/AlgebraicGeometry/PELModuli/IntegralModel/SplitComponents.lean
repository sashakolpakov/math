import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coproduct
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModelsHas
import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenPartitionIso

/-! # Split Components -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitComponents

noncomputable section

/-! Turn the actual split component decomposition supplied by SpreadingOut into
IntegralModel's categorical coproduct decomposition. The components are constructed
as open and closed subschemes, and their required geometry is inherited. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {B : Scheme} {r : ℕ} (S : Fin r → Over B)

def overCoproductIsoSigma : (∐ S) ≅ ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigma S :=
  Over.isoMk (Coproduct.underlyingCoproductIso S) (by
    change (Coproduct.underlyingCoproductIso S).hom ≫ Sigma.desc (fun i => (S i).hom) = (∐ S).hom
    apply (cancel_epi (Coproduct.underlyingCoproductIso S).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_comp_desc, ← Category.assoc, Coproduct.underlyingCoproductIso_ι]
    exact (Sigma.ι S i).w.symm)

theorem underlyingCoproductIso_hom_ι (i : Fin r) :
    (Sigma.ι S i).left ≫ (Coproduct.underlyingCoproductIso S).hom =
      Sigma.ι (fun j => (S j).left) i := by
  rw [← Coproduct.underlyingCoproductIso_ι]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (X : Over B)

/-- A split smooth proper scheme is an actual finite coproduct of smooth
proper geometrically connected components. Their inclusions are closed
immersions, so projectivity is retained whenever the whole scheme is
equipped with its projective presentation. -/
theorem split_components_decomposition [Smooth X.hom] [IsProper X.hom]
    (hX : ModelsHas.HasSplitGeometricComponents X) :
    ∃ (n : ℕ) (C : Fin n → Over B) (e : (∐ C) ≅ X),
      (∀ i, Smooth (C i).hom ∧ IsProper (C i).hom ∧ GeometricallyConnected (C i).hom ∧
        IsClosedImmersion (Sigma.ι C i ≫ e.hom).left) ∧
      (Components.RelativelyProjective X → ∀ i, Components.RelativelyProjective (C i)) := by
  obtain ⟨n, U, hdis, hcover, hconn⟩ := hX
  let C (i : Fin n) := ArithmeticGeometry.Models.SpreadingOut.OpenOver.Construction.overOpen X (U i)
  let e : (∐ C) ≅ X := overCoproductIsoSigma C ≪≫
    ArithmeticGeometry.Models.SpreadingOut.OpenPartitionIso.Construction.overOpenPartitionIso X U hdis hcover
  have hclosed (i) : IsClosedImmersion (U i).ι :=
    ArithmeticGeometry.Models.SpreadingOut.SplitCoproducts.Construction.open_partition_closedImmersion U hdis hcover i
  have he (i) : (Sigma.ι C i ≫ e.hom).left = (U i).ι := by
    change (Sigma.ι C i).left ≫
      (Coproduct.underlyingCoproductIso C).hom ≫ Sigma.desc (fun j => (U j).ι) = (U i).ι
    rw [← Category.assoc, underlyingCoproductIso_hom_ι]
    exact Sigma.ι_comp_desc (fun j => (U j).ι) i
  refine ⟨n, C, e, ?_, ?_⟩
  · intro i
    have := hclosed i
    exact ⟨inferInstanceAs (Smooth ((U i).ι ≫ X.hom)),
      inferInstanceAs (IsProper ((U i).ι ≫ X.hom)), hconn i, he i ▸ hclosed i⟩
  · rintro ⟨P⟩ i
    have := hclosed i
    exact ⟨{
      dimension := P.dimension
      embedding := ArithmeticGeometry.Models.SpreadingOut.OpenOver.Construction.overOpenInclusion X (U i) ≫ P.embedding
      closedImmersion := inferInstanceAs (IsClosedImmersion ((U i).ι ≫ P.embedding.left)) }⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitComponents
