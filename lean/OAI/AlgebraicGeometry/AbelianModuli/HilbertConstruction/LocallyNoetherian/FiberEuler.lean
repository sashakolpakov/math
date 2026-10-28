import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FiberEuler

/-! # Fiber Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FiberEuler

noncomputable section

/-! Genuine fiber Euler characteristic is locally constant on every locally Noetherian base of a proper flat line-bundle family. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem locallyNoetherian_properFlat_fiberEuler_isLocallyConstant
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) :
    IsLocallyConstant (Geometric.FiberEuler.fiberEulerCharacteristic f L) := by
  have hlocal (U : S.affineOpens) :
      IsLocallyConstant (fun y : U.1.toScheme => Geometric.FiberEuler.fiberEulerCharacteristic f L (U.1.ι y)) := by
    have : IsAffine U.1.toScheme := U.2
    have : IsLocallyNoetherian U.1.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.1.ι
    have : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
    let H := IsPullback.of_hasPullback f U.1.ι
    have hfun : (fun y : U.1.toScheme => Geometric.FiberEuler.fiberEulerCharacteristic f L (U.1.ι y)) =
        Geometric.FiberEuler.fiberEulerCharacteristic (pullback.snd f U.1.ι) (L.pullback (pullback.fst f U.1.ι)) := by
      funext y
      exact (Open.FiberEuler.fiberEulerCharacteristic_openBaseChange H L y).symm
    rw [hfun]
    exact ProperFlat.FiberEuler.properFlat_fiberEuler_isLocallyConstant (pullback.snd f U.1.ι) (L.pullback (pullback.fst f U.1.ι))
  apply (IsLocallyConstant.iff_exists_open (Geometric.FiberEuler.fiberEulerCharacteristic f L)).mpr
  intro x
  have hx : x ∈ iSup (fun U : S.affineOpens => U.1) := by rw [iSup_affineOpens_eq_top]; trivial
  obtain ⟨U, hUx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let xU : U.1.toScheme := ⟨x, hUx⟩
  obtain ⟨V, hV, hxV, hconst⟩ := (hlocal U).exists_open xU
  refine ⟨U.1.ι '' V, U.1.ι.isOpenMap V hV, ⟨xU, hxV, rfl⟩, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  exact hconst y hy

theorem locallyNoetherian_properFlat_groundFieldFiberEuler_isLocallyConstant
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) :
    IsLocallyConstant (fun x : S =>
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)).sheaf) := by
  have hfun : (fun x : S =>
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic (f.fiberToSpecResidueField x) (L.pullback (f.fiberι x)).sheaf) =
        Geometric.FiberEuler.fiberEulerCharacteristic f L := by
    funext x
    exact (FiberEulerGroundField.fiberEulerCharacteristic_eq_groundField f L x).symm
  rw [hfun]
  exact locallyNoetherian_properFlat_fiberEuler_isLocallyConstant f L

theorem locallyNoetherian_properFlat_fiberEuler_eq_of_preconnected
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [PreconnectedSpace S]
    (f : X ⟶ S) [IsProper f] [Flat f] (L : Line.Bundles.LineBundle X) (x y : S) :
    Geometric.FiberEuler.fiberEulerCharacteristic f L x = Geometric.FiberEuler.fiberEulerCharacteristic f L y :=
  (locallyNoetherian_properFlat_fiberEuler_isLocallyConstant f L).apply_eq_of_preconnectedSpace x y

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.FiberEuler
