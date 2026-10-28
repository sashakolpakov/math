import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicInvariantDescent
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterGluing

/-! # Framed Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedRecovery.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: effective recovery preserves the actual character scalar
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- An intertwining isomorphism gives the same endomorphism in the transported frames. -/
theorem conjugate_intertwiner {C : Type*} [Category C] {A B M N U : C}
    (e : A ≅ M) (d : B ≅ N) (u : M ≅ U) (v : N ≅ U)
    (a : A ⟶ B) (b : M ⟶ N) (h : e.hom ≫ b = a ≫ d.hom) :
    (e ≪≫ u).inv ≫ a ≫ (d ≪≫ v).hom = u.inv ≫ b ≫ v.hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc a d.hom v.hom, ← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Pulling back a composite frame retains the supplied module isomorphism. -/
theorem pulledModuleFrame_trans {X T : Scheme.{u}} {L M : X.Modules}
    (e : L ≅ M) (d : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (x : T ⟶ X) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (e ≪≫ d) x =
      (Scheme.Modules.pullback x).mapIso e ≪≫ Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d x := by
  apply Iso.ext
  simp only [Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (D E : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f)
    (e : D.module ≅ E.module) (d : E.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

/-- A compatible recovery preserves the exact regular function defining the gluing. -/
theorem framedDescentScalar_eq_of_recovery {T : Scheme.{u}} (q : T ⟶ Y)
    (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (h : DescentRelationMorphisms.Construction.LineDescent.CompatibleAt D E e.hom q x y hx hy) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D (e ≪≫ d) q x y hx hy = Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar E d q x y hx hy := by
  apply congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T)
  unfold Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentEnd
  rw [pulledModuleFrame_trans, pulledModuleFrame_trans]
  exact conjugate_intertwiner ((Scheme.Modules.pullback x).mapIso e)
    ((Scheme.Modules.pullback y).mapIso e) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d x) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d y)
    _ _ h

variable (C : ScalarLineGluing.Construction.LineDescent.ScalarCocycle f) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (r : (Scheme.Modules.pullback f).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

/-- Recovery of scalar gluing returns the original scalar, not just its isomorphism class. -/
theorem scalarCocycle_recovery {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q)
    (h : DescentRelationMorphisms.Construction.LineDescent.CompatibleAt (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf) C.nativeDatum r.hom q x y hx hy) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf) r q x y hx hy = C.value q x y hx hy := by
  have hs := framedDescentScalar_eq_of_recovery (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf) C.nativeDatum
    r (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) q x y hx hy h
  have he : r ≪≫ Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) = r := Iso.trans_refl r
  have hn := congrArg (fun a => Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf) a q x y hx hy) he
  exact hn.symm.trans (hs.trans (C.nativeDatum_scalar q x y hx hy))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedRecovery.Construction.LineDescent
