import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitComponents
import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts

/-! # Component Coproduct -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentCoproduct

noncomputable section

/-! Finite arithmetic component coproducts are smooth and proper, and
their actual inclusions inherit projectivity from the whole scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction

theorem component_coproduct_smooth_proper
    {R : Type} [CommRing R] {r : ℕ} (S : Fin r → Over (Spec (.of R)))
    (hS : ∀ i, Smooth (S i).hom ∧ IsProper (S i).hom) :
    Smooth (∐ S).hom ∧ IsProper (∐ S).hom := by
  let Y := ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.overSigma S
  have : Smooth Y.hom := by
    let : IsZariskiLocalAtSource (@Smooth.{0}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) (fun i => (hS i).1)
  have : IsProper Y.hom := ArithmeticGeometry.Models.SpreadingOut.ProperCoproducts.Construction.proper_finite_sigma_desc R (fun i => (S i).hom) (fun i => (hS i).2)
  let e := SplitComponents.overCoproductIsoSigma S
  have : IsIso e.hom.left := ((Over.forget (Spec (.of R))).mapIso e).isIso_hom
  rw [← e.hom.w]
  exact ⟨inferInstance, inferInstance⟩

theorem decomposition_inclusion_closed
    {B : Scheme} {r : ℕ} (S : Fin r → Over B) {X : Over B} (e : (∐ S) ≅ X) (i : Fin r) :
    IsClosedImmersion (Sigma.ι S i ≫ e.hom).left := by
  have : IsOpenImmersion (Sigma.ι S i ≫ e.hom).left := Coproduct.decomposition_inclusion_open S e i
  apply IsClosedImmersion.of_isPreimmersion
  have h : Topology.IsClosedEmbedding (fun x : (S i).left => Coproduct.decompositionHomeomorph S e ⟨i, x⟩) :=
    (Coproduct.decompositionHomeomorph S e).isClosedEmbedding.comp Topology.IsClosedEmbedding.sigmaMk
  have he : (fun x : (S i).left => Coproduct.decompositionHomeomorph S e ⟨i, x⟩) =
      (Sigma.ι S i ≫ e.hom).left := funext (Coproduct.decompositionHomeomorph_apply S e i)
  rw [he] at h
  exact h.isClosed_range

theorem projective_components_of_decomposition
    {B : Scheme} {r : ℕ} (S : Fin r → Over B) {X : Over B} (e : (∐ S) ≅ X)
    (hX : Components.RelativelyProjective X) (i : Fin r) : Components.RelativelyProjective (S i) := by
  obtain ⟨P⟩ := hX
  have : IsClosedImmersion (Sigma.ι S i ≫ e.hom).left := decomposition_inclusion_closed S e i
  exact ⟨⟨P.dimension, (Sigma.ι S i ≫ e.hom) ≫ P.embedding,
    inferInstanceAs (IsClosedImmersion ((Sigma.ι S i ≫ e.hom).left ≫ P.embedding.left))⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentCoproduct
