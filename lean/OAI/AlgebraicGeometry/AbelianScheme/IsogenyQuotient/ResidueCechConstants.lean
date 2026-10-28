import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalCechConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Residue Cech Constants -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ResidueCechConstants.Construction

noncomputable section

/-! The actual residue fiber supplies exactness of the native Cech
augmentation over the local ring's residue field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

set_option backward.isDefEq.respectTransparency false in
theorem properSmoothPointed_fieldBaseChange_globalFunctions_isIso
    {S X : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    {K : Type u} [Field K] (s : Spec (.of K) ⟶ S) :
    IsIso (pullback.snd f s).appTop := by
  let b := pullback.snd f s
  have : IsReduced (pullback f s) := AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smoothOverField_isReduced b
  have : ConnectedSpace (pullback f s : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton b
  let σ' : Spec (.of K) ⟶ pullback f s :=
    pullback.lift (s ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  exact (AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants.properConnectedReducedPointGlobalIso b σ' (pullback.lift_snd _ _ _)).isIso_hom

set_option backward.isDefEq.respectTransparency false in
theorem residueCech_constants_exact
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} [X.IsSeparated] (f : X ⟶ Spec (.of R))
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (hU : iSup U = ⊤) (ha : ∀ i, IsAffineOpen (U i)) :
    Function.Exact ((Relative.CechConstants.Construction.relativeCechConstants f U hU).lTensor (IsLocalRing.ResidueField R))
      (((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom.lTensor (IsLocalRing.ResidueField R)) := by
  let m := IsLocalRing.maximalIdeal R
  have : IsIso (pullback.snd f (FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec m 0)).appTop := by
    have : (m ^ (0 + 1)).IsMaximal := by
      simpa only [Nat.zero_add, pow_one] using (inferInstance : m.IsMaximal)
    let : Field (R ⧸ m ^ (0 + 1)) := Ideal.Quotient.field _
    exact properSmoothPointed_fieldBaseChange_globalFunctions_isIso f σ hσ
      (K := R ⧸ m ^ (0 + 1)) (FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec m 0)
  let P (J : Ideal R) := Function.Exact ((Relative.CechConstants.Construction.relativeCechConstants f U hU).lTensor (R ⧸ J))
    (((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom.lTensor (R ⧸ J))
  have hh : P (m ^ (0 + 1)) := InfinitesimalCechConstants.Construction.infinitesimalCech_constants_exact m f U hU ha 0
  have hm : m ^ (0 + 1) = m := by simp
  have hh' : P m := hm ▸ hh
  exact hh'

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ResidueCechConstants.Construction
