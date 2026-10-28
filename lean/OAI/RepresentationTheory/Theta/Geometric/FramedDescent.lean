import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames
import OAI.RepresentationTheory.Theta.Geometric.OrdinaryDescentIsomorphisms
import OAI.RepresentationTheory.Theta.Geometric.FactoredPullbackFrames
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineMorphismDescent

/-! # Framed Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.FramedDescent

noncomputable section

/-! A frame invariant under ordinary descent gives a trivial descended
line bundle. The construction retains arbitrary scheme test objects. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
universe u

theorem unitFrame_composite_eq {X Y T : Scheme.{u}} (f : X ⟶ Y)
    (q : T ⟶ Y) (x : T ⟶ X) (hx : x ≫ f = q) :
    (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app
        (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) ≫ (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso q).hom =
      (Pullback.FrameComposition.pullbackGlobalFrame x (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f)).hom := by
  cases hx
  exact congrArg Iso.hom (Pullback.FrameComposition.pullbackUnitIso_comp x f)

theorem canonicalUnit_frame {X Y T : Scheme.{u}} (f : X ⟶ Y)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    ((AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj
      (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
        (Pullback.FrameComposition.pullbackGlobalFrame y (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f)).hom =
      (Pullback.FrameComposition.pullbackGlobalFrame x (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f)).hom := by
  rw [show ((AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj
      (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      (AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)).hom q x y hx hy from rfl,
    AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom,
    ← unitFrame_composite_eq f q y hy]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact unitFrame_composite_eq f q x hx

theorem framedDatum_compatible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
        (Pullback.FrameComposition.pullbackGlobalFrame y e).hom = (Pullback.FrameComposition.pullbackGlobalFrame x e).hom)
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullback x).map (e ≪≫ (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).symm).hom ≫
      ((AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)).hom
        q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
        (Scheme.Modules.pullback y).map (e ≪≫ (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).symm).hom := by
  apply (cancel_mono (Pullback.FrameComposition.pullbackGlobalFrame y (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f)).hom).mp
  simp only [Category.assoc]
  rw [canonicalUnit_frame]
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Pullback.FrameComposition.pullbackGlobalFrame,
    Functor.mapIso_hom, Category.assoc, Iso.map_inv_hom_id_assoc] using (he q x y hx hy).symm

def framedDatumIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)
    (he : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
        (Pullback.FrameComposition.pullbackGlobalFrame y e).hom = (Pullback.FrameComposition.pullbackGlobalFrame x e).hom) :
    D ≅ (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :=
  OrdinaryDescentIsomorphisms.nativeDescentIsoMk f D _ (e ≪≫ (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso f).symm)
    (framedDatum_compatible f D e he)

theorem lineIso_of_descentIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (L M : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (e : (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L.sheaf ≅
      (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M.sheaf) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  obtain ⟨d, _⟩ := AlgebraicGeometry.Picard.Homomorphisms.LineMorphismDescent.Construction.exists_lineIso_of_compatible_pullbackIso f L M (OrdinaryDescentIsomorphisms.nativeDescentObjIso f e)
    (fun q x y hx hy => OrdinaryDescentIsomorphisms.nativeDescentObjIso_compatible f e q x y hx hy)
  exact ⟨d⟩

end

end OAI.RepresentationTheory.Theta.Geometric.FramedDescent
