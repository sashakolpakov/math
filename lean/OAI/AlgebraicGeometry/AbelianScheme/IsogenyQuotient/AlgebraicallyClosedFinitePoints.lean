import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Lean.Util.CollectAxioms

/-! # Algebraically Closed Finite Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedFinitePoints.Construction

noncomputable section

/-! Every field-valued point of a quasi-finite scheme over an
algebraically closed field is defined over that field. The result
retains the specified point and the exact factorization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosed_quasiFinite_point_factors
    {k K : Type} [Field k] [IsAlgClosed k] [Field K]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    (u : Spec (.of K) ⟶ Spec (.of k)) (p : Spec (.of K) ⟶ X) (hp : p ≫ f = u) :
    ∃ r : Spec (.of k) ⟶ X, r ≫ f = 𝟙 _ ∧ u ≫ r = p := by
  have : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite f
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective p
  have hx : IsClosed ({x} : Set X) := isClosed_singleton
  let e := residueFieldIsoBase f x hx
  have he : X.fromSpecResidueField x ≫ f ≫ Spec.map e.hom = 𝟙 _ := by
    rw [← Category.assoc, ← SpecMap_residueFieldIsoBase_inv f x hx,
      ← Spec.map_comp, e.hom_inv_id, Spec.map_id]
  refine ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx, ?_⟩
  change u ≫ (Spec.map e.hom ≫ X.fromSpecResidueField x) =
    Spec.map a ≫ X.fromSpecResidueField x
  change (Spec.map a ≫ X.fromSpecResidueField x) ≫ f = u at hp
  rw [← hp]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun q => Spec.map a ≫ q ≫ X.fromSpecResidueField x) he

set_option backward.isDefEq.respectTransparency false in
theorem algebraicallyClosed_quasiFinite_points_bijective
    {k K : Type} [Field k] [IsAlgClosed k] [Field K]
    (X : Over (Spec (.of k))) [LocallyQuasiFinite X.hom] [LocallyOfFiniteType X.hom]
    (u : Spec (.of K) ⟶ Spec (.of k)) :
    Function.Bijective (fun r : Over.mk (𝟙 (Spec (.of k))) ⟶ X =>
      (Over.homMk u (Category.comp_id u) : Over.mk u ⟶ Over.mk (𝟙 _)) ≫ r) := by
  have : Surjective u := ⟨Function.surjective_to_subsingleton _⟩
  constructor
  · intro r s h
    apply Over.OverMorphism.ext
    exact (cancel_epi u).mp (congrArg Over.Hom.left h)
  · intro p
    obtain ⟨r, hr, he⟩ := algebraicallyClosed_quasiFinite_point_factors X.hom u p.left p.w
    exact ⟨Over.homMk r hr, Over.OverMorphism.ext he⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedFinitePoints.Construction
