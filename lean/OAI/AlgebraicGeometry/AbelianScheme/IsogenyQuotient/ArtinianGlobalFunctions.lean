import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NilpotentCechGlobalFunctions
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechFlat
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalCechConstants
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PointedFiniteCechCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Artinian Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArtinianGlobalFunctions.Construction

noncomputable section

/-! A proper smooth family with connected geometric fibers and a
section has exactly the base functions over an Artinian local ring.
The proof uses the actual residue fiber and retains all nilpotents. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

set_option backward.isDefEq.respectTransparency false in
theorem artinianLocal_globalFunctions_isIso
    {R : Type u} [CommRing R] [IsArtinianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Smooth f] [GeometricallyConnected f]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _) : IsIso f.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by
    have : IsSeparated (f ≫ terminal.from (Spec (.of R))) := inferInstance
    simpa only [terminal.comp_from] using this⟩
  have : Subsingleton (Spec (.of R)) := Ring.KrullDimLE.subsingleton_primeSpectrum R
  obtain ⟨I, hIfin, hIorder, U, hUa, hU, a, ha⟩ := PointedFiniteCechCover.Construction.exists_pointed_finite_cech_cover σ
  let := hIfin
  let := hIorder
  let m := IsLocalRing.maximalIdeal R
  have hm : IsNilpotent m := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
  have : Module.Flat R ((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X 1) := Relative.CechFlat.Construction.relativeStructureCech_flat f U hUa 1
  have : (m ^ (0 + 1)).IsMaximal := by
    simpa only [Nat.zero_add, pow_one] using (inferInstance : m.IsMaximal)
  let : Field (R ⧸ m ^ (0 + 1)) := Ideal.Quotient.field _
  let j := FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec m 0
  let b := pullback.snd f j
  have : Smooth b := inferInstanceAs (Smooth (pullback.snd f j))
  have : IsProper b := inferInstanceAs (IsProper (pullback.snd f j))
  have : GeometricallyConnected b := inferInstanceAs (GeometricallyConnected (pullback.snd f j))
  have : IsReduced (pullback f j) := AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smoothOverField_isReduced (K := R ⧸ m ^ (0 + 1)) b
  have : Subsingleton (FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction.infinitesimalBase m 0) :=
    inferInstanceAs (Subsingleton (Spec (.of (R ⧸ m ^ (0 + 1)))))
  have : Nonempty (FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction.infinitesimalBase m 0) :=
    inferInstanceAs (Nonempty (Spec (.of (R ⧸ m ^ (0 + 1)))))
  have : ConnectedSpace (pullback f j : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton b
  let σ' : FormalGeometry.Completion.Infinitesimal.Neighborhoods.Construction.infinitesimalBase m 0 ⟶ pullback f j :=
    pullback.lift (j ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  have : IsIso b.appTop := (AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants.properConnectedReducedPointGlobalIso
    (K := R ⧸ m ^ (0 + 1)) b σ' (pullback.lift_snd _ _ _)).isIso_hom
  apply NilpotentCechGlobalFunctions.Construction.globalFunctions_iso_of_nilpotent_cech (m ^ (0 + 1))
    (by simpa only [Nat.zero_add, pow_one] using hm) f σ hσ U hU a ha
  exact InfinitesimalCechConstants.Construction.infinitesimalCech_constants_exact m f U hU hUa 0

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ArtinianGlobalFunctions.Construction
