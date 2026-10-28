import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PicardFaithfullyFlat
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality

/-! # Picard Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PicardInjection.Construction

noncomputable section

/-! A field extension detects equality of actual line-bundle classes
on a pointed family with universal global functions. In particular it
detects all line-class identities on abelian varieties and their products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false in
theorem pointed_field_picard_pullback_injective
    {k : Type} [Field k] {X Y : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) (x : Spec (.of k) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (hX : GlobalFunctions.Construction.HasUniversalGlobalFunctions (Over.mk p))
    (u : Y ⟶ Spec (.of k)) [Flat u] [Surjective u] [QuasiCompact u] :
    Function.Injective (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst p u)) := by
  intro l m h
  obtain ⟨L, rfl⟩ := Quotient.exists_rep l
  obtain ⟨M, rfl⟩ := Quotient.exists_rep m
  obtain ⟨e⟩ := Quotient.exact h
  let F := AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M
  let T : Over (Spec (.of k)) := Over.mk (𝟙 _)
  let U : Over (Spec (.of k)) := Over.mk u
  let v : U ⟶ T := Over.homMk u (Category.comp_id u)
  have : Flat v.left := inferInstanceAs (Flat u)
  have : Surjective v.left := inferInstanceAs (Surjective u)
  have : QuasiCompact v.left := inferInstanceAs (QuasiCompact u)
  let R : Sieve T := {
    arrows V _ := Nonempty (F.obj (.op V))
    downward_closed := by
      intro V W f he g
      exact he.map (F.map g.op) }
  have hv : R v := by
    let c := pullbackSymmetry u p
    exact ⟨((Scheme.Modules.pullbackComp c.hom (pullback.fst p u)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (pullbackSymmetry_hom_comp_fst u p)).app L.sheaf).symm ≪≫
      (Scheme.Modules.pullback c.hom).mapIso e ≪≫
      (Scheme.Modules.pullbackComp c.hom (pullback.fst p u)).app M.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (pullbackSymmetry_hom_comp_fst u p)).app M.sheaf⟩
  have hR : R ∈ (Scheme.fpqcTopology.over (Spec (.of k))) T := by
    apply (Scheme.fpqcTopology.over (Spec (.of k))).superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (Universal.PicardFaithfullyFlat.Construction.fpqcSingletonOverSieve_mem v)
    intro V f hf
    obtain ⟨i⟩ := hf
    exact hv
  have hi := AbelianModuli.HilbertConstruction.Normalized.BundleIsoDescent.relativeBundleIso_nonempty_of_cover p x hx L M
    ((L.pullback x).trivialization_of_subsingleton ≪≫
      (M.pullback x).trivialization_of_subsingleton.symm)
    Scheme.fpqcTopology (Universal.BundleNormalization.Construction.universal_familyBaseChangeSection_bijective p x hx hX)
    T R hR (fun _ hf => hf)
  exact Quotient.sound ((AbelianModuli.HilbertConstruction.IsoIdentityBaseChange.relativeBundleIso_identity_nonempty_iff p L M).mp hi)

theorem field_abelian_picard_pullback_injective
    {k : Type} [Field k] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    {Y : Scheme.{0}} (u : Y ⟶ Spec (.of k)) [Flat u] [Surjective u] [QuasiCompact u] :
    Function.Injective (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullback.fst A.scheme.hom u)) :=
  pointed_field_picard_pullback_injective A.scheme.hom η[A.scheme].left η[A.scheme].w
    (GlobalFunctions.Construction.fieldAbelian_hasUniversalGlobalFunctions A) u

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PicardInjection.Construction
