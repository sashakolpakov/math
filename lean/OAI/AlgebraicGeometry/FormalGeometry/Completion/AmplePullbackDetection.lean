import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.GlobalFunctions
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TorsionLine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Ample Pullback Detection -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.AmplePullbackDetection

noncomputable section

/-! A map from a proper integral geometric scheme is constant if it pulls
an ample line bundle back to the trivial bundle. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]

theorem properIntegral_constant_of_trivial_ample_pullback
    (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ p = 𝟙 _)
    (f : X ⟶ Y) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (hL : L.IsAmple)
    (hf : (L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : f = p ≫ e ≫ f := by
  let x : X := Classical.choice inferInstance
  obtain ⟨n, _hn, s, hx, hs⟩ := (L.isAmple_iff_tensorPower.mp hL).2 (f x)
  let P := (L.tensorPower n).pullback f
  let ep : P.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
    Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso f L n ≪≫ (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X n).mapIso hf ≪≫ AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerUnitIso X n
  let ep1 : (P.tensorPower 1).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
    ((P.tensorPower_isTensorPower 1).unique (AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one P.sheaf)).some ≪≫ ep
  let t := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s
  have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s :=
    Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f (L.tensorPower n) s
  have htx : x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := ht.symm ▸ hx
  have : IsProper (Over.mk p).hom := inferInstanceAs (IsProper p)
  have : ConnectedSpace (Over.mk p).left := inferInstanceAs (ConnectedSpace X)
  have : IsReduced (Over.mk p).left := inferInstanceAs (IsReduced X)
  have : IsIso t := Quotients.FiniteDescent.TorsionLine.Construction.TorsionLineBundle.isIso_of_nonempty_nonvanishing
    (Over.mk p) P 1 (by omega) ep1 t ⟨x, htx⟩
  have htop : f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s = ⊤ := ht.symm.trans (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso t)
  let U := AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
  have : IsAffine U.toScheme := hs
  have hrange : Set.range f ⊆ Set.range U.ι := by
    rintro y ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : z ∈ f ⁻¹ᵁ U := by rw [htop]; trivial
    exact hz
  let g := IsOpenImmersion.lift U.ι f hrange
  have hg : g ≫ U.ι = f := IsOpenImmersion.lift_fac U.ι f hrange
  have h := congrArg (fun a : X ⟶ U.toScheme => a ≫ U.ι)
    (Proper.GlobalFunctions.Construction.properIntegral_to_affine_constant p e he g)
  simpa only [Category.assoc, hg] using h

theorem groupHom_eq_one_of_trivial_ample_pullback
    {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B]
    [IsProper A.hom] [GeometricallyIntegral A.hom]
    (f : A ⟶ B) [IsMonHom f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left) (hL : L.IsAmple)
    (hf : (L.pullback f.left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) : f = 1 := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have h := properIntegral_constant_of_trivial_ample_pullback A.hom
    (MonObj.one (X := A)).left (MonObj.one (X := A)).w f.left L hL hf
  have hunit : (MonObj.one (X := A)).left ≫ f.left = (MonObj.one (X := B)).left :=
    congrArg Over.Hom.left (IsMonHom.one_hom f)
  apply Over.OverMorphism.ext
  change f.left = A.hom ≫ (MonObj.one (X := B)).left
  simpa only [hunit] using h

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.AmplePullbackDetection
