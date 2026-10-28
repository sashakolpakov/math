import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomBaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedModuleHomDescent

/-! # Open Frame Descent -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenFrameDescent

noncomputable section

/-! Restrict compatible descent data to an actual open subscheme of the
base and descend the morphism where both base modules have frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}

theorem nativeDescentHom_compatible
    {D E : PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)} (b : D ⟶ E)
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullback x).map (b.hom PUnit.unit) ≫
        (IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f E).hom q x y hx hy =
      (IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D).hom q x y hx hy ≫
        (Scheme.Modules.pullback y).map (b.hom PUnit.unit) :=
  b.comm q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy

def openDescentHom (U : Y.Opens)
    (b : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M) :=
  ModuleHomBaseChange.Construction.baseChangedDescentHom f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι (morphismRestrict_ι f U).symm b

def openDescentModuleHom (U : Y.Opens)
    (b : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M) :
    (Scheme.Modules.pullback (f ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj L) ⟶
      (Scheme.Modules.pullback (f ∣_ U)).obj ((Scheme.Modules.pullback U.ι).obj M) :=
  ModuleHomBaseChange.Construction.canonicalDescentModuleHom (f ∣_ U) (openDescentHom f U b)

theorem existsUnique_descent_on_frame_open [Flat f] [Surjective f] [QuasiCompact f]
    (U : Y.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (d : (Scheme.Modules.pullback U.ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (b : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M) :
    ∃! a : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj M,
      (Scheme.Modules.pullback (f ∣_ U)).map a = openDescentModuleHom f U b := by
  have : Surjective (f ∣_ U) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  exact FramedModuleHomDescent.Construction.existsUnique_framed_moduleHom_descent (f ∣_ U) e d (openDescentModuleHom f U b)
    (fun q x y hx hy => nativeDescentHom_compatible (f ∣_ U) (openDescentHom f U b) q x y hx hy)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenFrameDescent
