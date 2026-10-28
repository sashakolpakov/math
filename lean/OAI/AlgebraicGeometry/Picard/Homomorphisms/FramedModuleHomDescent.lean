import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentMorphisms
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitEndDescent

/-! # Framed Module Hom Descent -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedModuleHomDescent

noncomputable section

/-! Faithfully flat descent of module morphisms when the two modules
have frames on the base. This is the local calculation for line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}
variable (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (d : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)

include e d in
theorem pullbackHom_injective_of_frames [Epi f] :
    Function.Injective ((Scheme.Modules.pullback f).map : (L ⟶ M) → _) := by
  intro a b hab
  apply (Iso.homCongr e d).injective
  apply UnitEndDescent.Construction.unitEndPullback_injective f
  exact (FramedDescentMorphisms.Construction.unitEndPullback_framedMap e d a f).trans
    ((congrArg (fun t => (FramedDescentScalars.Construction.pulledModuleFrame e f).inv ≫ t ≫ (FramedDescentScalars.Construction.pulledModuleFrame d f).hom) hab).trans
      (FramedDescentMorphisms.Construction.unitEndPullback_framedMap e d b f).symm)

include e d in
theorem existsUnique_framed_moduleHom_descent [EffectiveEpi f]
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    (hb : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x).map b ≫ (CanonicalDescentFrames.Construction.canonicalModuleDescent f M).hom q x y hx hy =
        (CanonicalDescentFrames.Construction.canonicalModuleDescent f L).hom q x y hx hy ≫ (Scheme.Modules.pullback y).map b) :
    ∃! a : L ⟶ M, (Scheme.Modules.pullback f).map a = b := by
  let eX := FramedDescentScalars.Construction.pulledModuleFrame e f
  let dX := FramedDescentScalars.Construction.pulledModuleFrame d f
  let c : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := eX.inv ≫ b ≫ dX.hom
  have hc : ∀ {T : Scheme.{u}} (x y : T ⟶ X), x ≫ f = y ≫ f →
      UnitPullbackScalars.Construction.unitEndPullback x c = UnitPullbackScalars.Construction.unitEndPullback y c := by
    intro T x y hxy
    let q := x ≫ f
    have hx : x ≫ f = q := rfl
    have hy : y ≫ f = q := hxy.symm
    have h := FramedDescentMorphisms.Construction.framedDescent_morphism (CanonicalDescentFrames.Construction.canonicalModuleDescent f L) (CanonicalDescentFrames.Construction.canonicalModuleDescent f M)
      eX dX b q x y hx hy (hb q x y hx hy)
    have hD := CanonicalDescentFrames.Construction.canonicalModuleDescent_framedEnd f L e q x y hx hy
    have hE := CanonicalDescentFrames.Construction.canonicalModuleDescent_framedEnd f M d q x y hx hy
    exact (Category.comp_id (UnitPullbackScalars.Construction.unitEndPullback x c)).symm.trans
      ((congrArg (fun t => UnitPullbackScalars.Construction.unitEndPullback x c ≫ t) hE).symm.trans
        (h.trans ((congrArg (fun t => t ≫ UnitPullbackScalars.Construction.unitEndPullback y c) hD).trans
          (Category.id_comp (UnitPullbackScalars.Construction.unitEndPullback y c)))))
  obtain ⟨a₀, ha₀, _⟩ := UnitEndDescent.Construction.existsUnique_unitEnd_descent f c hc
  let a : L ⟶ M := e.hom ≫ a₀ ≫ d.inv
  have hnorm : eX.inv ≫ (Scheme.Modules.pullback f).map a ≫ dX.hom =
      UnitPullbackScalars.Construction.unitEndPullback f a₀ := by
    dsimp [eX, dX, a, FramedDescentScalars.Construction.pulledModuleFrame, UnitPullbackScalars.Construction.unitEndPullback]
    simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  have ha : (Scheme.Modules.pullback f).map a = b := by
    apply (Iso.homCongr eX dX).injective
    exact hnorm.trans ha₀
  exact ⟨a, ha, fun a' ha' => pullbackHom_injective_of_frames f e d (ha'.trans ha.symm)⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedModuleHomDescent
