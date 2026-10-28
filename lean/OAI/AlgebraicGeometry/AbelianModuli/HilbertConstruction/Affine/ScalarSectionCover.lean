import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoproductCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentEpimorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Coproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Scalar Section Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ScalarSectionCover

noncomputable section

/-! Epimorphic scalar sections on an affine scheme generate the unit ideal. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace
universe u

theorem affine_scalar_sections_span {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Fintype ι]
    (s : ι → End (Line.Bundles.structureModule X)) [Epi (Sigma.desc s)] :
    Ideal.span (Set.range (fun i => Frame.Coordinates.structureModuleEndValue X (s i))) = ⊤ := by
  have hunit : (Line.Bundles.structureModule X).IsQuasicoherent := (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  have : (∐ fun _ : ι => Line.Bundles.structureModule X).IsQuasicoherent :=
    Quasicoherent.Coproducts.module_quasicoherent_coproduct _ (fun _ => hunit)
  let F : X.Modules ⥤ ModuleCat Γ(X, ⊤) := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let : F.Additive := { map_add := by intros; ext; rfl }
  let : HasBiproduct (fun _ : ι => Line.Bundles.structureModule X) := HasBiproduct.of_hasCoproduct _
  obtain ⟨x, hx⟩ := QuasicoherentEpimorphisms.quasicoherent_affine_surjective_of_epi (Sigma.desc s) (1 : Γ(X, ⊤))
  let c : ι → Γ(X, ⊤) := fun i =>
    F.map (Finite.CoproductCoordinates.finiteCoproductProjection (fun _ : ι => Line.Bundles.structureModule X) i) x
  let t : ι → Γ(X, ⊤) → Γ(X, ⊤) := fun i z => (s i).app ⊤ z
  have hsum : ∑ i, c i * Frame.Coordinates.structureModuleEndValue X (s i) = 1 := by
    have h := Finite.CoproductCoordinates.finiteCoproduct_desc_value F (fun _ : ι => Line.Bundles.structureModule X) s x
    change (show Γ(X, ⊤) from ((Sigma.desc s).app ⊤) x) = ∑ i, t i (c i) at h
    change (show Γ(X, ⊤) from ((Sigma.desc s).app ⊤) x) = (1 : Γ(X, ⊤)) at hx
    have hi (i : ι) : t i (c i) = c i * Frame.Coordinates.structureModuleEndValue X (s i) :=
      TensorPower.Units.structureModuleEnd_app (s i) ⊤ (c i)
    have he : (∑ i, c i * Frame.Coordinates.structureModuleEndValue X (s i)) = ∑ i, t i (c i) :=
      Finset.sum_congr rfl (fun i _ => (hi i).symm)
    exact he.trans (h.symm.trans hx)
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  rw [← hsum]
  apply Submodule.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

theorem affine_scalar_sections_cover {X : Scheme.{u}} [IsAffine X] {ι : Type u} [Fintype ι]
    (s : ι → End (Line.Bundles.structureModule X)) [Epi (Sigma.desc s)] :
    ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  have hU := iSup_basicOpen_of_span_eq_top (⊤ : X.Opens)
    (Set.range (fun i => Frame.Coordinates.structureModuleEndValue X (s i))) (affine_scalar_sections_span s)
  intro x
  have hx : x ∈ ⨆ r ∈ Set.range (fun i => Frame.Coordinates.structureModuleEndValue X (s i)), X.basicOpen r := by
    rw [hU]
    trivial
  obtain ⟨r, hr⟩ := Opens.mem_iSup.mp hx
  obtain ⟨⟨i, rfl⟩, hi⟩ := Opens.mem_iSup.mp hr
  exact ⟨i, (Scalar.Nonvanishing.sectionNonvanishing_scalar (s i)).symm ▸ hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ScalarSectionCover
