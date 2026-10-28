import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicDescentRecovery
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedRecovery

/-! # Line Recovery Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineRecoveryUniqueness.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: uniquely recovered line isomorphisms, with their actual frames
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [QuasiCompact f]

/-- A compatible pullback isomorphism descends uniquely, with its exact original map. -/
theorem existsUnique_lineIso_descent (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : (Scheme.Modules.pullback f).obj L.sheaf ≅ (Scheme.Modules.pullback f).obj M.sheaf)
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf) (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf)
        e.hom q x y hx hy) :
    ∃! a : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback f).map a.hom = e.hom := by
  let b := Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentHom f e.hom he
  let c := Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentHom f e.inv (fun q x y hx hy =>
    LineCharacterDetection.Construction.LineDescent.inverse_intertwines ((Scheme.Modules.pullback x).mapIso e) ((Scheme.Modules.pullback y).mapIso e)
      ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf).hom q x y hx hy)
      ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf).hom q x y hx hy) (he q x y hx hy))
  obtain ⟨a, ha, _⟩ := LineHomDescent.Construction.LineDescent.existsUnique_lineHom_descent f L M b
  obtain ⟨d, hd, _⟩ := LineHomDescent.Construction.LineDescent.existsUnique_lineHom_descent f M L c
  have ha' : (Scheme.Modules.pullback f).map a = e.hom := ha
  have hd' : (Scheme.Modules.pullback f).map d = e.inv := hd
  have had : a ≫ d = 𝟙 L.sheaf := by
    apply LineHomDescent.Construction.LineDescent.pullbackHom_injective_lines f L L
    rw [Functor.map_comp, ha', hd', e.hom_inv_id, CategoryTheory.Functor.map_id]
  have hda : d ≫ a = 𝟙 M.sheaf := by
    apply LineHomDescent.Construction.LineDescent.pullbackHom_injective_lines f M M
    rw [Functor.map_comp, hd', ha', e.inv_hom_id, CategoryTheory.Functor.map_id]
  refine ⟨⟨a, d, had, hda⟩, ha', ?_⟩
  intro a' ha''
  exact Iso.ext (LineHomDescent.Construction.LineDescent.pullbackHom_injective_lines f L M (ha''.trans ha'.symm))

/-- Recovery of one ordinary datum determines the descended line and its recovery map uniquely. -/
theorem nativeLineRecovery_unique
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L.sheaf ≅ D)
    (d : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M.sheaf ≅ D) :
    ∃! a : L.sheaf ≅ M.sheaf,
      (Scheme.Modules.pullback f).map a.hom ≫ d.hom.hom PUnit.unit = e.hom.hom PUnit.unit := by
  let c := e ≪≫ d.symm
  let c₀ := (Picard.Homomorphisms.ModuleHomBaseChange.Construction.nativeDescentEvaluation f).mapIso c
  have hc : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf) (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf)
        c₀.hom q x y hx hy := by
    intro T q x y hx hy
    exact c.hom.comm q x y hx hy
  obtain ⟨a, ha, hu⟩ := existsUnique_lineIso_descent f L M c₀ hc
  have hd : IsIso (d.hom.hom PUnit.unit) :=
    ((Picard.Homomorphisms.ModuleHomBaseChange.Construction.nativeDescentEvaluation f).mapIso d).isIso_hom
  have hcd : c₀.hom ≫ d.hom.hom PUnit.unit = e.hom.hom PUnit.unit := by
    have h : (e ≪≫ d.symm).hom ≫ d.hom = e.hom := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg (fun b => b.hom PUnit.unit) h
  refine ⟨a, (congrArg (fun b => b ≫ d.hom.hom PUnit.unit) ha).trans hcd, ?_⟩
  intro a' ha'
  apply hu a'
  exact (cancel_mono (d.hom.hom PUnit.unit)).mp (ha'.trans hcd.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineRecoveryUniqueness.Construction.LineDescent
